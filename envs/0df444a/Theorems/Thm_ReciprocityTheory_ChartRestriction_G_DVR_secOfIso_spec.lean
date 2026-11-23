-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secOfIso_spec
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:25.871862+00:00
-- url     : https://prove2.me/theorems/14c4e29a-5b0d-4e37-b3d9-b95793df1b9d
-- title:
--   DVR: sec Of Iso spec
-- statement:
--   The DVR construction uses the sec Of Iso spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L346-L348

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {Y : Scheme.{0}} {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B)
variable {u}

theorem ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) (a : A.ι) (b : B.ι) :
    rs (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) ((secOfIso t hu hA hB).f a) = isoCand u t a b := by sorry
