-- Prove2me | Theorems.Thm_P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08
-- name    : P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:56.362984+00:00
-- url     : https://prove2.me/theorems/fbbb8204-40eb-4df1-9449-eb5185a42e03
-- title:
--   P2 M Formalism FG Solve VAux low pow sub  02c94c820c08: P2 M Formalism FG Solve VAux low pow sub  02c94c820c08
-- statement:
--   The P2 M Formalism FG Solve VAux low pow sub  02c94c820c08 construction uses the P2 M Formalism FG Solve VAux low pow sub  02c94c820c08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L99-L109

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}

theorem P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08 {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hkk : ∀ i, Low M (k i - k' i))
    (e : ι →₀ ℕ) : Low M (P k e - P k' e) := by sorry

alias «Formalism».«FG».«SolveVAux».«low_pow_sub₂» := P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08
