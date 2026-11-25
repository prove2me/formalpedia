-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4
-- name    : P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:15.262951+00:00
-- url     : https://prove2.me/theorems/a9723fd2-7c36-4ba2-b8fa-b3302ad9d763
-- title:
--   P2 M Global Theory Tau Bal Pull val  one 971f3d4236f4: P2 M Global Theory Tau Bal Pull val  one 971f3d4236f4
-- statement:
--   The P2 M Global Theory Tau Bal Pull val  one 971f3d4236f4 construction uses the P2 M Global Theory Tau Bal Pull val  one 971f3d4236f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L109-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4 {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {K : Type} [Fintype K]
    {ψ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L ψ ε))
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (lift η[A] η[A]).left) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by sorry

alias «GlobalTheory».«TauBalPull».«val₂_one» := P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4
