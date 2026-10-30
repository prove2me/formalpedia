-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma10
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:54:31.596313+00:00
-- url     : https://prove2.me/theorems/c84feba7-a2cd-433a-a6e6-c33b39a3a7fb
-- title:
--   Lemma 10: single-factor partial trace of a physical block
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. For every allowed adjacent pair, the physical block satisfies
--
--   $$\operatorname{Tr}_nF_\mu(\alpha)=\frac{m_\alpha}{m_\mu}P_\mu.$$
--
--   The direction of the ratio follows also by taking total traces: both sides have trace $m_\alpha d_\mu$. This supplies the input-register trace required by the joint dual.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 13, Lemma 10: single-factor partial trace of a physical block

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

/-- PDF pp.13,29 Lemma10: the ratio is m_alpha/m_mu, confirmed by Eq.(115). -/
theorem lemma10 (d k : ℕ) (hd : 2 ≤ d)
    (a : Schur.Partition d (k+1)) (b : Schur.Partition d (k+2)) (hab : Extends a b) :
    traceFinalQudits 1 (fBlock a b) = ((mult a:ℂ)/(mult b:ℂ)) •
      Schur.isotypicProjector b := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
