-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact5
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:50:37.585721+00:00
-- url     : https://prove2.me/theorems/25df9e27-c869-4983-8111-c76fe0afc786
-- title:
--   Fact 5: Bell-weighted partial trace of a physical block
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. For every allowed adjacent pair $(\alpha,\mu)$, use the actual physical block $F_\mu(\alpha)$ and the unnormalized Bell operator $B_{Nn}$. Then
--
--   $$\operatorname{Tr}_{N,n}[B_{Nn}F_\mu(\alpha)]=\frac{m_\mu}{m_\alpha}P_\alpha.$$
--
--   Using the trace-one Bell projector instead would divide the right side by $d$. This identity controls the dual pair-trace constraints.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 11, Fact 5: Bell-weighted partial trace of a physical block

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

/-- PDF pp.11,27–28 Fact5: B is unnormalized, so the ratio is m_mu/m_alpha. -/
theorem fact5 (d k : ℕ) (hd : 2 ≤ d)
    (a : Schur.Partition d (k+1)) (b : Schur.Partition d (k+2)) (hab : Extends a b) :
    traceFinalQudits 2 (unnormalizedPortBell d (k+2) (Fin.last (k+1)) * fBlock a b) =
      ((mult b:ℂ)/(mult a:ℂ)) • Schur.isotypicProjector a := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
