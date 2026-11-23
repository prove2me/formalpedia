-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_algebraMap_ne_zero
-- name    : ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.algebraMap_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:20.624808+00:00
-- url     : https://prove2.me/theorems/ba296261-885f-4535-9043-531d83070f17
-- title:
--   Second Cohomology Lattice: algebra Map ne zero
-- statement:
--   The Second Cohomology Lattice construction uses the algebra Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsSmulMemOfMemSpan.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsSmulMemOfMemSpan.lean#L29-L31

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_Lemmata_MiscLemmasL_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
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
open Module
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.algebraMap_ne_zero [IsFractionRing R C] {r : R} (hr : r ≠ 0) : algebraMap R C r ≠ 0 := by sorry
