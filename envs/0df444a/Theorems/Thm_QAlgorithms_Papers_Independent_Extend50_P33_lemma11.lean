-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma11
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:55:13.744462+00:00
-- url     : https://prove2.me/theorems/40dfd78e-6de9-45f1-9e26-78eb9e767e12
-- title:
--   Lemma 11: jointly optimized dual witness
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Put $p=N/(N+d^2-1)$, $b=p/d^N$, and $\Omega=d\eta/(N+d^2-1)$. This actual matrix is positive and obeys every pair constraint $\operatorname{Tr}_{a,n}[Q_{an}\Omega]\succeq I$ and the corrected input trace constraint $bI-d^{-(N+1)}\operatorname{Tr}_n\Omega\succeq0$. Thus
--
--   $$p_{\rm dual}=d^Nb=\frac{N}{N+d^2-1},\qquad p_{\rm feasible}\le p_{\rm dual}.$$
--
--   The input trace corrects the register typo in printed Eq.(28), as required by Eqs.(119)–(121).
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 13, Lemma 11: jointly optimized dual witness

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

/-- PDF pp.13,29–30 Lemma11: actual dual d eta/(N+d²−1), with corrected
input-register trace in the third constraint. -/
theorem lemma11 (d k : ℕ) (hd : 2 ≤ d) :
    JointDual (jointOmega d k)
      (optimalProbability d (k+2) / (d:ℝ)^(k+2)) ∧
    (∀ p ∈ jointValues d k, p ≤ optimalProbability d (k+2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
