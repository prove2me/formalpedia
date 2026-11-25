-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LamBiext_formEq__cd7eb449d15c
-- name    : P2M_GlobalTheory_LamBiext_formEq__cd7eb449d15c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:09.912813+00:00
-- url     : https://prove2.me/theorems/61b07552-c255-4075-a028-df8b5d71bd42
-- title:
--   P2 M Global Theory Lam Biext form Eq  cd7eb449d15c: P2 M Global Theory Lam Biext form Eq  cd7eb449d15c
-- statement:
--   The P2 M Global Theory Lam Biext form Eq  cd7eb449d15c construction uses the P2 M Global Theory Lam Biext form Eq  cd7eb449d15c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L172-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L172-L183

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

theorem P2M_GlobalTheory_LamBiext_formEq__cd7eb449d15c : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := by sorry

alias «GlobalTheory».«LamBiext».«formEq₂» := P2M_GlobalTheory_LamBiext_formEq__cd7eb449d15c
