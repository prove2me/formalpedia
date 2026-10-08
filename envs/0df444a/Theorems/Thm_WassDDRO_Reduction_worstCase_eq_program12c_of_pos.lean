-- Prove2me | Theorems.Thm_WassDDRO_Reduction_worstCase_eq_program12c_of_pos
-- name    : WassDDRO.Reduction.worstCase_eq_program12c_of_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:28.984181+00:00
-- url     : https://prove2.me/theorems/988f707f-be8e-43fc-9ede-e1859500f369
-- title:
--   Proof of Theorem 4.2, p. 13 — under Assumption 4.1, (12a) is an equality for every ε > 0
-- statement:
--   Let $E$, $\Xi$, $\ell=\max_{k\le K}\ell_k$ and the samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ be as in Theorem 4.2 ($K,N\ge1$, each $\ell_k$ measurable), and suppose Assumption 4.1 holds: $\Xi$ is convex and closed, each $-\ell_k$ is proper, convex and lower semicontinuous, and no $\ell_k$ is identically $-\infty$ on $\Xi$. Then for every $\varepsilon>0$
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]=\inf_{\lambda\ge0,\ s\in\mathbb R^N}\Big\{\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\ :\ \sup_{\xi\in\Xi}\big(\ell(\xi)-\lambda\|\xi-\hat\xi_i\|\big)\le s_i\ \ \forall i\Big\},$$
--   that is, the max-min inequality (12a) holds with equality and (10) equals the optimal value of (12c).
--
--   This is the strong-duality step of the proof, an instance of strong duality for moment problems.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, p. 13 (equality in (12a) for ε > 0)

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, p. 13: under Assumption 4.1 the inequality (12a) is an equality
for any `ε > 0`, i.e. (10) equals the optimal value of (12c). -/
theorem worstCase_eq_program12c_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hεpos : 0 < ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program12cValue ε Ξ ξhat (maxLoss ℓ) := by sorry

end WassDDRO.Reduction
