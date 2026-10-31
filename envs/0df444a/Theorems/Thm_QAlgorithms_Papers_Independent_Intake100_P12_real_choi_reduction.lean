-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_real_choi_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.real_choi_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:03:40.731087+00:00
-- url     : https://prove2.me/theorems/7cd79507-7787-4cc7-b57f-b0e45c5502d5
-- title:
--   Real success and failure Choi matrices suffice
-- statement:
--   Let $d,k\ge1$, choose one of the three protocol classes, and choose either unitary transposition or inversion. Every achievable constant success probability $p$ can be achieved in that same class by a two-branch instrument $(S,F)$ with
--
--   $$\operatorname{Im} S_{ab}=\operatorname{Im}F_{ab}=0\quad\text{for all computational-basis indices }a,b.$$
--
--   Moreover the maximal achievable probability is attained by such an instrument. The success branch implements the target channel exactly for every $U\in U(d)$.
--
--   Real means entrywise real in the fixed bases; both branches and the protocol class are preserved.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 8, III, Eqs. (21)–(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.7–8, Eqs. (21)–(27): entrywise-real success AND failure branches
suffice in each chosen class; the maximum is attained by such an instrument. -/
theorem real_choi_reduction {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (c : ProtocolClass) (t : UnitaryTask) (ht : t = .transpose ∨ t = .inverse) :
    (∀ p, Attainable c d k (targetChoi t) p → ∃ S F,
      HeraldedRealizable c d k S F ∧ ExactUnitarySuccess S (targetChoi t) p ∧
      (∀ a b, (S a b).im = 0) ∧ (∀ a b, (F a b).im = 0)) ∧
    (∃ p S F, 0 ≤ p ∧ p ≤ 1 ∧ HeraldedRealizable c d k S F ∧
      ExactUnitarySuccess S (targetChoi t) p ∧ (∀ a b, (S a b).im = 0) ∧
      (∀ a b, (F a b).im = 0) ∧
      ∀ q, Attainable c d k (targetChoi t) q → q ≤ p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
