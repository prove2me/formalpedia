-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_spectrum_of
-- name    : PositivityTheory.Rg.Cz.spectrum_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:18.172037+00:00
-- url     : https://prove2.me/theorems/bf1c5d4b-1c7e-5b53-a407-c799b99d6347
-- title:
--   Cz: spectrum of
-- statement:
--   The Cz construction uses the spectrum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L296-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L296-L321

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz

theorem PositivityTheory.Rg.Cz.spectrum_of : TensorGl → JMComm → Curry → StepChar → Spectrum := by sorry
