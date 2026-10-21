-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_lockability_and_separation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.lockability_and_separation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:46:48.168008+00:00
-- url     : https://prove2.me/theorems/3e161924-69b6-41df-9797-bb43d67552bb
-- title:
--   §IV.G: lockability and unbounded c/q separation
-- statement:
--   Let $\phi_d$ be the tripartite flower state with local data dimension $d$ and a qubit flag at each party. For every real threshold $L$ there exists $d\ge1$ such that
--
--   $$E_F^t(\phi_d)>L,\qquad E_F^t(\operatorname{Tr}_{A'}\phi_d)=0\quad(t=q,c;\ F=I_3,S_3),$$
--   $$E_{I_3}^c(\phi_d)-E_{I_3}^q(\phi_d)>L.$$
--
--   The erased flag may be replaced by a local pure zero flag. Thus all four quantities are lockable and the total classical version exceeds the quantum one by an unbounded additive amount. No unbounded-ratio claim is made.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 8, §IV.G: lockability and unbounded c/q separation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.G, PDF pp.7–8: unbounded drops after one flag-qubit loss
for all four measures, and an unbounded ADDITIVE cI-qI difference.
There is no claim of an unbounded ratio or equality on mixed states. -/
theorem lockability_and_separation : ∀ L : ℝ, ∃ d : ℕ, 0 < d ∧
    (∀ (classical : Bool) (kind : InformationKind),
      L < multipartiteSquashed classical kind (multipartiteFlower 3 d) ∧
      multipartiteSquashed classical kind (eraseFlowerFlag (0 : Fin 3) (multipartiteFlower 3 d)) = 0) ∧
    L < multipartiteSquashed true .total (multipartiteFlower 3 d) - multipartiteSquashed false .total (multipartiteFlower 3 d) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
