-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:24.395799+00:00
-- url     : https://prove2.me/theorems/f2d5106e-9b56-5b21-a2cc-8af3af3ebde0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel diff Step single nat Cast 044387e002a6: P2 M Ground Theory Heights  Heights Hilbert Samuel diff Step single nat Cast 044387e002a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel diff Step single nat Cast 044387e002a6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel diff Step single nat Cast 044387e002a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L36-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6 (g : (K → ℤ) → ℤ) (m : K → ℕ) (k : K) :
    diffStep (Pi.single k 1) g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) =
      g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) - g (fun j => (m j : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«diffStep_single_natCast» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_diffStep_single_natCast_044387e002a6
