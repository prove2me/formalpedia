-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact13
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:58:26.448238+00:00
-- url     : https://prove2.me/theorems/978f33f6-52d9-4115-af5b-6eeebc7f5d02
-- title:
--   Fact 13: compatibility of algebra and Young projections
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. For each physical $\alpha$, let $M_\alpha$ be the support projection of the constructed $\eta(\alpha)$ and let $P_\alpha$ act on the first $N-1$ systems. For the unnormalized Bell operator $B_{Nn}$,
--
--   $$M_\alpha B_{Nn}=(P_\alpha\otimes I\otimes I)B_{Nn}.$$
--
--   This one-sided identity relates the algebra projection and Young projection on the Bell-supported subspace.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 17, Fact 13: compatibility of algebra and Young projections

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

/-- PDF p.17 Fact13: one-sided Bell compatibility, not equality of M and P. -/
theorem fact13 (d k : ℕ) (hd : 2 ≤ d) (a : Schur.Partition d (k+1)) :
    mBlock a * unnormalizedPortBell d (k+2) (Fin.last (k+1)) =
      tensorIdentityExtension 2 (Schur.isotypicProjector a) * unnormalizedPortBell d (k+2) (Fin.last (k+1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
