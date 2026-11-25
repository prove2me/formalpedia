-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LamBiext_formEq__87630df18372
-- name    : P2M_GlobalTheory_LamBiext_formEq__87630df18372
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:52.675794+00:00
-- url     : https://prove2.me/theorems/773134e1-84c4-4cc3-96a6-e206898a9841
-- title:
--   P2 M Global Theory Lam Biext form Eq  87630df18372: P2 M Global Theory Lam Biext form Eq  87630df18372
-- statement:
--   The P2 M Global Theory Lam Biext form Eq  87630df18372 construction uses the P2 M Global Theory Lam Biext form Eq  87630df18372 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L159-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L159-L170

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem P2M_GlobalTheory_LamBiext_formEq__87630df18372 : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := by sorry

alias «GlobalTheory».«LamBiext».«formEq₁» := P2M_GlobalTheory_LamBiext_formEq__87630df18372
