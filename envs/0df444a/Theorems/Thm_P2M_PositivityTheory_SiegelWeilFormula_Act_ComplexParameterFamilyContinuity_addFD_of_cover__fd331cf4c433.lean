-- Prove2me | Theorems.Thm_P2M_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover__fd331cf4c433
-- name    : P2M_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover__fd331cf4c433
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:11.16028+00:00
-- url     : https://prove2.me/theorems/decc2c72-708a-56d1-8d8e-15a9cfa09ca4
-- title:
--   P2 M Positivity Theory Siegel Weil Formula Act Complex Parameter Family Continuity add FD of cover  fd331cf4c433: P2 M Positivity Theory Siegel Weil Formula Act Complex Parameter Family Continuity add
-- statement:
--   The P2 M Positivity Theory Siegel Weil Formula Act Complex Parameter Family Continuity add FD of cover  fd331cf4c433 construction uses the P2 M Positivity Theory Siegel Weil Formula Act Complex Parameter Family Continuity add FD of cover  fd331cf4c433 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/AddFDOfCover.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/AddFDOfCover.lean#L44-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_AddFDOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

theorem P2M_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover__fd331cf4c433 {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [DiscreteTopology Γ] {C : Set A} (hC : IsCompact C)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ C) (μ : Measure A) :
    ∃ 𝓕 : Set A, IsAddFundamentalDomain Γ 𝓕 μ ∧ IsCompact (closure 𝓕) := by sorry

alias «PositivityTheory».«SiegelWeilFormula».«Act».«ComplexParameterFamilyContinuity».«addFD_of_cover'» := P2M_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover__fd331cf4c433
