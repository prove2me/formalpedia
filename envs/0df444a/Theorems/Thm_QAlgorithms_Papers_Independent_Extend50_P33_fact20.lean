-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact20
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:04:15.94945+00:00
-- url     : https://prove2.me/theorems/dd690078-8f55-4e7b-93b7-092fbda1378e
-- title:
--   Fact 20: invariance of Young projectors under swap conjugation
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. For the full $\mu$ isotypic projection in the natural action of $S_N$,
--
--   $$\sum_{a=1}^{N}V((a,N))P_\mu V((a,N))=NP_\mu.$$
--
--   The identity representative $a=N$ is included. A single tableau projection would not encode this central projector result.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 21, Fact 20: invariance of Young projectors under swap conjugation

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

/-- PDF p.21 Fact20 Eq.(68), full isotypic rather than single-tableau projection. -/
theorem fact20 (d k : ℕ) (hd : 2 ≤ d) (b : Schur.Partition d (k+2)) :
    (∑ a : Fin (k+2),
      Schur.tensorPermutation d (k+2) (Equiv.swap a (Fin.last (k+1))) *
        Schur.isotypicProjector b *
      Schur.tensorPermutation d (k+2) (Equiv.swap a (Fin.last (k+1)))) =
        (((k+2:ℕ):ℂ)) • Schur.isotypicProjector b := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
