-- Prove2me | Theorems.Thm_PhaseCut_Stable_lemma_A_1
-- name    : PhaseCut.Stable.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:37.786568+00:00
-- url     : https://prove2.me/theorems/5b010710-3c06-4a78-820d-a7ca672c72de
-- title:
--   Lemma A.1, p. 24 — ‖V^∥_PC − (Ax₀)(Ax₀)*‖₂ > 2C‖Ax₀‖₂‖b_{n,PC}‖₂
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$, $x_0 \in \mathbb{C}^p$, $C > 0$, $D = 2C + 2\sqrt{2} + 1$, and $b_{n,PC} \in \mathbb{R}^n$ with $\|b_{n,PC}\|_2 \le \|Ax_0\|_2$. Let $V_{PC}$ be a minimizer of problem (13) for $b = |Ax_0| + b_{n,PC}$ such that
--   $$\|V_{PC} - (Ax_0)(Ax_0)^*\|_2 > D\,\|Ax_0\|_2\,\|b_{n,PC}\|_2 ,$$
--   and let $V_{PC}^{/\!/} = AA^\dagger V_{PC} AA^\dagger$. Then
--   $$\|V_{PC}^{/\!/} - (Ax_0)(Ax_0)^*\|_2 > 2C\,\|Ax_0\|_2\,\|b_{n,PC}\|_2 .$$
--
--   In the proof of Theorem 4.7, $V_{PC}$ is a PhaseCut solution violating $D$-stability; the lemma transfers the violation to $V_{PC}^{/\!/}$, which is a Weak PhaseLift solution, with constant $2C$.
--
--   **Formalization Note.** "Under the assumptions and notations of Theorem 4.7" is spelled out as the hypotheses the proof uses: minimality of $V_{PC}$ in (13), $C > 0$, the bound $\|b_{n,PC}\|_2 \le \|Ax_0\|_2$ (the proof's "we assumed"), and the violated $D$-bound. Stability of Weak PhaseLift and $A \neq 0$ are not used and are not assumed. Norms are the Frobenius norm for matrices and the Euclidean norm for vectors.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, Lemma A.1, p. 24 (with the setting of the proof of Theorem 4.7, p. 14)

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **Lemma A.1** (p. 24). Let `C > 0` and `D = 2C + 2√2 + 1`. If `V_PC` minimizes (13) for
`b = |Ax₀| + b_{n,PC}`, `‖b_{n,PC}‖₂ ≤ ‖Ax₀‖₂` and `‖V_PC − (Ax₀)(Ax₀)*‖₂ > D ‖Ax₀‖₂ ‖b_{n,PC}‖₂`, then
`‖V^∥_PC − (Ax₀)(Ax₀)*‖₂ > 2C ‖Ax₀‖₂ ‖b_{n,PC}‖₂`. -/
theorem lemma_A_1 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) (C : ℝ) (hC : 0 < C)
    (bnPC : Fin n → ℝ) (VPC : Matrix (Fin n) (Fin n) ℂ)
    (hV : IsMin13 A (absAx A x₀ + bnPC) VPC)
    (hsmall : vnorm bnPC ≤ cnorm (A *ᵥ x₀))
    (hbad : (2 * C + 2 * Real.sqrt 2 + 1) * cnorm (A *ᵥ x₀) * vnorm bnPC
      < frob (VPC - outer A x₀)) :
    2 * C * cnorm (A *ᵥ x₀) * vnorm bnPC < frob (Vpar A VPC - outer A x₀) := by sorry
end PhaseCut.Stable
