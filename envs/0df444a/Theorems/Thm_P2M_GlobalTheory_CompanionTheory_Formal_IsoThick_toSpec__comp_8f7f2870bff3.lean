-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Formal_IsoThick_toSpec__comp_8f7f2870bff3
-- name    : P2M_GlobalTheory_CompanionTheory_Formal_IsoThick_toSpec__comp_8f7f2870bff3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:47.783832+00:00
-- url     : https://prove2.me/theorems/be96a797-def7-42f9-8125-9b52ec259df8
-- title:
--   P2 M Global Theory Companion Theory Formal Iso Thick to Spec  comp 8f7f2870bff3: P2 M Global Theory Companion Theory Formal Iso Thick to Spec  comp 8f7f2870bff3
-- statement:
--   The P2 M Global Theory Companion Theory Formal Iso Thick to Spec  comp 8f7f2870bff3 construction uses the P2 M Global Theory Companion Theory Formal Iso Thick to Spec  comp 8f7f2870bff3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L150-L153

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick

theorem P2M_GlobalTheory_CompanionTheory_Formal_IsoThick_toSpec__comp_8f7f2870bff3 {R : Type} [CommRing R] {X : Scheme.{0}} (h : X ⟶ Spec (CommRingCat.of R)) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop) = h := by sorry

alias «GlobalTheory».«CompanionTheory».«Formal».«IsoThick».«toSpecΓ_comp» := P2M_GlobalTheory_CompanionTheory_Formal_IsoThick_toSpec__comp_8f7f2870bff3
