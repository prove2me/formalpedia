-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_minorZ_of
-- name    : PositivityTheory.Rg.Sw.SP.minorZ_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:54.842362+00:00
-- url     : https://prove2.me/theorems/7e795869-57d2-55af-86a2-f5072d3324d2
-- title:
--   SP: minor Z of
-- statement:
--   The SP construction uses the minor Z of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorZ.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorZ.lean#L29-L38

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open Polynomial

theorem PositivityTheory.Rg.Sw.SP.minorZ_of (hF : MinorFormula) : MinorZ := by sorry
