-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_Common0Aux_dsum_subtype
-- name    : PositivityTheory.RgJS.Common0Aux.dsum_subtype
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:42.157947+00:00
-- url     : https://prove2.me/theorems/8b906d30-faa6-5792-814c-d3b8f1af24c6
-- title:
--   Common0 Aux: dsum subtype
-- statement:
--   The Common0 Aux construction uses the dsum subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L103-L109

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}

theorem PositivityTheory.RgJS.Common0Aux.dsum_subtype {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ι → ℂ) :
    ∑ i : {i // P i}, ∑ j : {i // P i}, f i j = ∑ i, ∑ j, if P i ∧ P j then f i j else 0 := by sorry
