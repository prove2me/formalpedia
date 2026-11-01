-- Prove2me | Theorems.Thm_PetzFisher_theorem_1_2_monotonicity
-- name    : PetzFisher.theorem_1_2_monotonicity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:46.2385+00:00
-- url     : https://prove2.me/theorems/e09a9481-4fbf-4324-a1ea-e47956aad811
-- title:
--   Theorem 1.2 — $\beta^*(\mathbb J^f_{\beta(D)})^{-1}\beta\le(\mathbb J^f_D)^{-1}$ (14) and $\beta\mathbb J^f_D\beta^*\le\mathbb J^f_{\beta(D)}$ (15)
-- statement:
--   Let $\beta:M_n\to M_m$ be a completely positive trace preserving mapping, let $\beta^*:M_m\to M_n$ be its adjoint with respect to the Hilbert–Schmidt inner product $\langle X,Y\rangle=\operatorname{Tr}X^*Y$, and let $f:\mathbb R^+\to\mathbb R^+$ be a matrix monotone function. Let $D\in M_n$ be positive invertible and assume $\beta(D)$ is positive invertible. Then
--
--   $$
--   \beta^*\big(\mathbb J^f_{\beta(D)}\big)^{-1}\beta\le\big(\mathbb J^f_D\big)^{-1} \tag{14}
--   $$
--
--   and
--
--   $$
--   \beta\,\mathbb J^f_D\,\beta^*\le\mathbb J^f_{\beta(D)} \tag{15}
--   $$
--
--   as operators on $M_n$, resp. $M_m$. Explicitly: for every complex $A\in M_n$, $\langle\beta A,(\mathbb J^f_{\beta(D)})^{-1}\beta A\rangle\le\langle A,(\mathbb J^f_D)^{-1}A\rangle$, and for every complex $X\in M_m$, $\langle X,\beta\mathbb J^f_D\beta^*X\rangle\le\langle X,\mathbb J^f_{\beta(D)}X\rangle$.
--
--   Inequality (15) is the monotonicity of the generalized variance, and (14) the monotonicity of the monotone metric $\gamma^f_D(A,A)=\langle A,(\mathbb J^f_D)^{-1}A\rangle$ under coarse-graining; (14) gives the monotonicity of the quantum Fisher information matrix (Theorem 2.3). The paper cites this result without proof.
--
--   **Formalization Note** Complete positivity means that $\mathrm{id}_r\otimes\beta$ is positive for every $r$. Matrix monotonicity is required for positive definite matrices of every size. $f$ is not assumed symmetric or normalized. The inequalities are between complex numbers, $z\le w$ meaning that $w-z$ is real and nonnegative. If $f$ vanishes identically on $(0,\infty)$, $(\mathbb J^f_D)^{-1}$ is not defined in the paper; Lean's convention $0^{-1}=0$ makes both sides of (14) and (15) zero there.
--
--   Differences from the source:
--   - generalization: f : ℝ⁺ → ℝ⁺ → f ≥ 0 on (0,∞); reason: weaker hypothesis; a nonnegative operator monotone f is either positive on (0,∞), which is the printed case, or zero there, where both sides of (14) and (15) are 0
--   - generalization: f(A) ≤ f(B) for positive matrices A ≤ B → for positive definite A ≤ B of every size; reason: weaker hypothesis, every matrix monotone function on ℝ⁺ satisfies it
--   - reading: β(D) unrestricted → β(D) positive definite; reason: 𝕁^f_{β(D)} and its inverse are defined (p.7) only for a positive invertible matrix, which (14) and (15) need
--   - encoding: operator inequalities on Mₙ, Mₘ → quadratic-form inequalities over all complex A, X in ComplexOrder, with ⟨A, β*Yβ A⟩ written ⟨βA, YβA⟩; reason: definition of the operator order and of the Hilbert–Schmidt adjoint
--   - encoding: Mₙ, Mₘ → complex matrices over finite index types; reason: Lean convention, same instances
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, Theorem 1.2, eqs. (14)–(15), p.9

import Mathlib
import Definitions.Def_PetzFisher_JMap
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, Theorem 1.2, p.9:
"Let `β : Mₙ → Mₘ` be a completely positive trace preserving mapping and `f : ℝ⁺ → ℝ⁺` be a matrix
monotone function. Then `β*(𝕁^f_{β(D)})^{-1}β ≤ (𝕁^f_D)^{-1}` (14) and `β𝕁^f_D β* ≤ 𝕁^f_{β(D)}` (15)."
The paper cites this result ([43]) and gives no proof.

Both inequalities are operator inequalities on `Mₙ`, resp. `Mₘ`, with the Hilbert–Schmidt inner
product `⟨X, Y⟩ = Tr Xᴴ Y`, and `β*` is the Hilbert–Schmidt adjoint of `β`:
(14) for every complex `A ∈ Mₙ`, `⟨βA, (𝕁^f_{β(D)})^{-1} βA⟩ ≤ ⟨A, (𝕁^f_D)^{-1} A⟩`
(the left side is `⟨A, β*(𝕁^f_{β(D)})^{-1}β A⟩`);
(15) for every complex `X ∈ Mₘ`, `⟨X, β 𝕁^f_D β* X⟩ ≤ ⟨X, 𝕁^f_{β(D)} X⟩`.
The inequalities are in `ℂ` with `ComplexOrder`.

**Formalization Note.** `Mₙ`, `Mₘ` are `Matrix I I ℂ`, `Matrix J J ℂ` for finite types. CPTP is the
published `Dependency50.P28.CPTP`, `β*` the published `Dependency50.P21.channelAdjoint`, matrix
monotonicity the published `Information100.P50.OperatorMonotone` (for positive definite `A ≤ B` of
every size, `f(A) ≤ f(B)`), and `(𝕁^f_D)^{-1}` the published `Bridge50.P31.inverseMetric`. `D` is a
positive invertible matrix (standing assumption of §1.2, p.7) and so is `β(D)`, the matrix at which
`𝕁^f_{β(D)}` and its inverse are defined (p.7). `f` is not assumed symmetric or normalized. -/
theorem theorem_1_2_monotonicity {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (f : ℝ → ℝ)
    (hf : QAlgorithms.Papers.Independent.Information100.P50.OperatorMonotone f)
    (hfpos : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (β : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hβ : QAlgorithms.Papers.Independent.Dependency50.P28.CPTP β)
    (D : Matrix I I ℂ) (hD : D.PosDef) (hβD : (β D).PosDef) :
    (∀ A : Matrix I I ℂ,
      ((β A)ᴴ * QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f (β D) (β A)).trace ≤
        (Aᴴ * QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f D A).trace) ∧
    (∀ X : Matrix J J ℂ,
      (Xᴴ * β (JMap f D (QAlgorithms.Papers.Independent.Dependency50.P21.channelAdjoint β X))).trace ≤
        (Xᴴ * JMap f (β D) X).trace) := by sorry

end PetzFisher
