-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_corollary_2
-- name    : PrivacyParadox.Alloc.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:24.599481+00:00
-- url     : https://prove2.me/theorems/ff3d797f-d52c-4f0b-a198-a1e4ac3805c3
-- title:
--   Corollary 2, p. 14 (discrete form: Case 1 of the proof of Theorem 2, (56)–(57), p. 27) — under (56), A_k ∝ 1/√φ_k and p ≡ 1 are a saddle point
-- statement:
--   In the discrete program (39), assume the low-budget condition (56):
--   $$(B/s-l)\big(2\gamma+\bar\theta^*(1-\bar\theta^*)(1-\gamma)s\big)<\gamma\sqrt{\phi_1}\sum_{k=1}^K\pi_k\sqrt{\phi_k}.$$
--   Let
--   $$A^*_k=\frac{1}{\sqrt{\phi_k}}\cdot\frac{B/s-l}{\sum_{j=1}^K\pi_j\sqrt{\phi_j}}\quad(57),\qquad p^*_k=1 .$$
--   Then $A^*$ is feasible and strictly decreasing in $k$, $p^*$ is a best response to $A^*$ ($U(A^*,p)\le U(A^*,p^*)$ for every admissible $p$), and $A^*$ is a best response to $p^*$ ($U(A^*,p^*)\le U(A,p^*)$ for every feasible $A$).
--
--   This is the discrete form of Corollary 2: when the budget is low, the optimal allocation is inversely proportional to the square root of the virtual cost over the whole range, hence strictly decreasing, and the mechanism is strictly truthful by Theorem 1.
--
--   **Formalization Note** The paper states Corollary 2 for continuous costs (p. 14, (23)–(24)) and proves it as Case 1 of the discrete proof of Theorem 2 (App. D, p. 38); this item is that discrete statement.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 14, Corollary 2; App. C, pp. 27–28, Case 1, (56)–(57); App. D, p. 38

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem corollary_2 (P : Prog) (hP : P.Standing)
    (h56 : (P.B / P.s - P.l) * (2 * P.gam + P.theta * (1 - P.theta) * (1 - P.gam) * P.s) <
      P.gam * Real.sqrt (P.phi 1) * ∑ k ∈ Finset.Icc 1 P.K, P.pr k * Real.sqrt (P.phi k)) :
    let Astar : ℕ → ℝ := fun k => 1 / Real.sqrt (P.phi k) *
      ((P.B / P.s - P.l) / ∑ j ∈ Finset.Icc 1 P.K, P.pr j * Real.sqrt (P.phi j))
    let pstar : ℕ → ℝ := fun _ => 1
    P.FeasA Astar ∧ StrictAntiOn Astar (Set.Icc 1 P.K) ∧
      (∀ p : ℕ → ℝ, P.AdmP p → P.U Astar p ≤ P.U Astar pstar) ∧
      (∀ A : ℕ → ℝ, P.FeasA A → P.U Astar pstar ≤ P.U A pstar) := by sorry

end PrivacyParadox.Alloc
