-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma4
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:49:38.894197+00:00
-- url     : https://prove2.me/theorems/e9238665-b5a5-4ccd-b58a-baf03f3ee486
-- title:
--   Lemma 4: achievable fixed-resource primal value (corrected missing N)
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $t_\alpha=\min_{\mu\in\alpha}\gamma_\mu(\alpha)^{-1}$ and $\Theta_a=d\sum_\alpha t_\alpha P_{\alpha,\bar a}$. These explicit auxiliary operators are feasible and achieve
--
--   $$p=\frac{N}{d^N}\sum_\alpha m_\alpha d_\alpha t_\alpha.$$
--
--   Each minimum exists and is positive. The factor $N$ corrects the printed Lemma 4 according to the first evaluated terms of Eq.(102) and the objective Eq.(19). This provides the attainable primal value.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 11, Lemma 4: achievable fixed-resource primal value (corrected missing N)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.11,27 Lemma4, corrected: printed 1/d^N loses the factor N;
Eq.(19) and the first evaluated terms of Eq.(102) force N/d^N. -/
theorem lemma4 (d k : ℕ) (hd : 2 ≤ d) :
    FixedFeasible (fixedTheta d k) ∧ pbtSuccessProbability (fixedTheta d k) = fixedValue d k ∧
    (∀ a : Schur.Partition d (k+1),
      IsLeast (reciprocalSet a) (minReciprocal a) ∧ 0 < minReciprocal a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
