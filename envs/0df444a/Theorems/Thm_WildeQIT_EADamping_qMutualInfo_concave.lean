-- Prove2me | Theorems.Thm_WildeQIT_EADamping_qMutualInfo_concave
-- name    : WildeQIT.EADamping.qMutualInfo_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:41.495092+00:00
-- url     : https://prove2.me/theorems/033cbcef-74c8-4c2b-86d4-60734e2c7833
-- title:
--   Theorem 13.4.2 (concavity of the mutual information in the input state): $\sum_x p_X(x)I(A;B)_{\rho^x}\le I(A;B)_\sigma$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel on finite-dimensional systems, let $p_X$ be a probability distribution on a finite set $\mathcal X$, and for each $x$ let $\varphi^x_{AA'}$ be a pure state, with $\rho^x_{AB}\equiv\mathcal N_{A'\to B}(\varphi^x_{AA'})$. Let $\sigma_{A'}\equiv\sum_x p_X(x)\rho^x_{A'}$ be the average input state, let $\varphi_{AA'}$ be any purification of $\sigma_{A'}$, and let $\sigma_{AB}\equiv\mathcal N_{A'\to B}(\varphi_{AA'})$. Then
--
--   $$
--   \sum_x p_X(x)\,I(A;B)_{\rho^x}\le I(A;B)_\sigma .
--   $$
--
--   So the mutual information of a channel is a concave function of the input density operator, which makes its maximization a convex optimization problem; Proposition 21.6.2 uses it to restrict to diagonal inputs.
--
--   **Formalization Note** Finite dimensions, logarithms base 2. The states $\varphi^x_{AA'}$ are unit vectors on `r × a` with a common reference `r`; the purification $\varphi_{AA'}$ is a unit vector on `s × a` with its own reference `s` of any finite dimension, and "purification of $\sigma_{A'}$" is the hypothesis $\operatorname{Tr}_A\varphi_{AA'}=\sum_x p_X(x)\operatorname{Tr}_A\varphi^x_{AA'}$.
--
--   Differences from the source:
--   - encoding: $\varphi_{AA'}$ a purification of $\sigma_{A'}$ on an unspecified reference $A$ → a unit vector on `s × a` for any finite type `s` with $\operatorname{Tr}_A\varphi=\sigma_{A'}$; reason: this is the definition of a purification, with the reference dimension left free as in the book
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4.2, Theorem 13.4.2, p. 410, (13.137)

import Definitions.Def_WildeQIT_EADamping_idTensorApply
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_partialTrace

namespace WildeQIT.EADamping

open WildeQIT

/-- **Theorem 13.4.2 (concavity of the mutual information in the input state).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.4.2, (13.137),
p. 410: `∑ₓ p_X(x) I(A; B)_{ρˣ} ≤ I(A; B)_σ`, where `ρˣ_{AB} ≡ N_{A′→B}(φˣ_{AA′})`,
`σ_{A′} ≡ ∑ₓ p_X(x) ρˣ_{A′}`, `φ_{AA′}` is a purification of `σ_{A′}`, and
`σ_{AB} ≡ N_{A′→B}(φ_{AA′})`.

**Formalization Note.** Finite dimensions, bits. `I(A; B)` is the published
`DattaDiscord.mutualInfo` (`H(A) + H(B) − H(AB)`, von Neumann entropy in bits). `p` is a probability distribution on a finite
set `X`. The states `φˣ_{AA′}` are pure, unit vectors on `r × a` with a common reference `r`
(left factor); the purification `φ_{AA′}` is a unit vector on `s × a` with its own reference `s`
of any finite dimension, whose `A′` marginal `Tr_A φ` (`partialTraceLeft`) is `σ_{A′}`. -/
theorem qMutualInfo_concave {X r s a b : Type} [Fintype X] [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QChannel a b) (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (φ : X → EuclideanSpace ℂ (r × a)) (hφ : ∀ x, ‖φ x‖ = 1)
    (ψ : EuclideanSpace ℂ (s × a)) (hψ : ‖ψ‖ = 1)
    (hpur : partialTraceLeft (QAlgorithms.pureDensity ψ) =
      ∑ x, (p x : ℂ) • partialTraceLeft (QAlgorithms.pureDensity (φ x))) :
    ∑ x, p x * DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity (φ x))) ≤
      DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity ψ)) := by sorry

end WildeQIT.EADamping
