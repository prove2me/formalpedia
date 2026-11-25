-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_PLsAbs2_exists_ne_zero_of_iSup
-- name    : PositivityTheory.Rg.Rs.PLsAbs2.exists_ne_zero_of_iSup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:28.364724+00:00
-- url     : https://prove2.me/theorems/d1cac057-1880-5217-ac57-76cac2d18491
-- title:
--   PLs Abs2: exists ne zero of i Sup
-- statement:
--   The PLs Abs2 construction uses the exists ne zero of i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/ExistsNeZeroOfISup.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/ExistsNeZeroOfISup.lean#L9-L37

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_ExistsNeZeroOfISup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PLsAbs2

theorem PositivityTheory.Rg.Rs.PLsAbs2.exists_ne_zero_of_iSup {R M S : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] {ι : Type} (fs : ι → S →ₗ[R] M)
    (htop : ⨆ i, LinearMap.range (fs i) = ⊤) (x : M) (hx : x ≠ 0) : ∃ p : M →ₗ[R] S, p x ≠ 0 := by sorry
