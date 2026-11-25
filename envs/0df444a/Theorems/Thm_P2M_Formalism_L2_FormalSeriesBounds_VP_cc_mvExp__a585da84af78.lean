-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_VP_cc_mvExp__a585da84af78
-- name    : P2M_Formalism_L2_FormalSeriesBounds_VP_cc_mvExp__a585da84af78
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:49.680898+00:00
-- url     : https://prove2.me/theorems/042398de-6577-53d5-8b96-9dfa54ae72e9
-- title:
--   P2 M Formalism L2 Formal Series Bounds VP cc mv Exp  a585da84af78: P2 M Formalism L2 Formal Series Bounds VP cc mv Exp  a585da84af78
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds VP cc mv Exp  a585da84af78 construction uses the P2 M Formalism L2 Formal Series Bounds VP cc mv Exp  a585da84af78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L17-L19

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP

theorem P2M_Formalism_L2_FormalSeriesBounds_VP_cc_mvExp__a585da84af78 {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp h) = 1 := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«VP».«cc_mvExp'» := P2M_Formalism_L2_FormalSeriesBounds_VP_cc_mvExp__a585da84af78
