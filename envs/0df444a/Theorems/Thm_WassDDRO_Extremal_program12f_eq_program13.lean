-- Prove2me | Theorems.Thm_WassDDRO_Extremal_program12f_eq_program13
-- name    : WassDDRO.Extremal.program12f_eq_program13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:56:30.823907+00:00
-- url     : https://prove2.me/theorems/3a567f92-94b1-45bf-91ad-8f672e9a4209
-- title:
--   Proof of Theorem 4.4, pp. 15–16 — under Assumption 4.1, the optimal values of (12f) and (13) coincide
-- statement:
--   Let $N, K \ge 1$, let samples $\hat\xi_1, \dots, \hat\xi_N$ lie in $\Xi$, let $\varepsilon \ge 0$, and let $\ell_1, \dots, \ell_K : E \to \overline{\mathbb R}$ be measurable and satisfy Assumption 4.1. Then
--   $$\inf_{\lambda, s_i, z_{ik}} \Big\{\lambda\varepsilon + \frac1N\sum_{i=1}^N s_i \ :\ [-\ell_k + \chi_\Xi]^*(z_{ik}) - \langle z_{ik}, \hat\xi_i\rangle \le s_i,\ \|z_{ik}\|_* \le \lambda\ \ \forall i,k\Big\}$$
--   equals
--   $$\sup_{\alpha_{ik}, q_{ik}} \Big\{\frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\ell_k\Big(\hat\xi_i - \frac{q_{ik}}{\alpha_{ik}}\Big) \ :\ \frac1N\sum_{i,k}\|q_{ik}\| \le \varepsilon,\ \sum_k \alpha_{ik} = 1,\ \alpha_{ik} \ge 0,\ \hat\xi_i - \frac{q_{ik}}{\alpha_{ik}} \in \Xi\Big\},$$
--   that is, the optimal value of program (12f) equals the optimal value of program (13), with the conventions of p. 14 for $\alpha_{ik} = 0$.
--
--   This is the first part of the proof of Theorem 4.4. It is a statement about two finite-dimensional programs and does not involve probability measures; combined with the identity (10) = (12f) from the proof of Theorem 4.2, it gives the first claim of Theorem 4.4.
--
--   **Formalization Note** Both sides are `EReal` values of programs over feasibility predicates (see the Setting definitions). The measurability hypothesis on $\ell_k$ is the paper's standing assumption on the pieces (p. 11); it is not used by this finite-dimensional statement but kept for uniformity.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.4, (14a)–(14g), pp. 15–16

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

namespace WassDDRO.Extremal

/-- First part of the proof of Theorem 4.4, pp. 15–16: under Assumption 4.1 the optimal value
of (12f) equals the optimal value of (13), for every ε ≥ 0 (Lagrangian dual (14a), (14b),
minimax (14c), Lemma 4.5, (14d)–(14g), rescaling). -/
theorem program12f_eq_program13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    program12fValue ε Ξ ξhat ℓ = program13Value ε Ξ ξhat ℓ := by sorry

end WassDDRO.Extremal
