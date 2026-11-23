-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_map_tensorSpan
-- name    : ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.map_tensorSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:09.22833+00:00
-- url     : https://prove2.me/theorems/e05dca72-7eab-4124-ab0a-cd563be77424
-- title:
--   Second Cohomology Lattice: map tensor Span
-- statement:
--   The Second Cohomology Lattice construction uses the map tensor Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean#L9-L20

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by sorry
