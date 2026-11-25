-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_VP_addOf_eq__cf4b6669b69a
-- name    : P2M_Formalism_L2_FormalSeriesBounds_VP_addOf_eq__cf4b6669b69a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:08.547441+00:00
-- url     : https://prove2.me/theorems/b8318b01-40c3-5a4b-af7b-9bea0ca7e245
-- title:
--   P2 M Formalism L2 Formal Series Bounds VP add Of eq  cf4b6669b69a: P2 M Formalism L2 Formal Series Bounds VP add Of eq  cf4b6669b69a
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds VP add Of eq  cf4b6669b69a construction uses the P2 M Formalism L2 Formal Series Bounds VP add Of eq  cf4b6669b69a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L28-L36

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
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
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)

theorem P2M_Formalism_L2_FormalSeriesBounds_VP_addOf_eq__cf4b6669b69a {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«VP».«addOf_eq'» := P2M_Formalism_L2_FormalSeriesBounds_VP_addOf_eq__cf4b6669b69a
