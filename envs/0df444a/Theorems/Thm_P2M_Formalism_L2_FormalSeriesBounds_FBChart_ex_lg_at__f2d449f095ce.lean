-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_FBChart_ex_lg_at__f2d449f095ce
-- name    : P2M_Formalism_L2_FormalSeriesBounds_FBChart_ex_lg_at__f2d449f095ce
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:08:34.518797+00:00
-- url     : https://prove2.me/theorems/b2ed48d4-1cf2-455c-bfaf-a4f42b2a10a6
-- title:
--   P2 M Formalism L2 Formal Series Bounds FBChart ex lg at  f2d449f095ce: P2 M Formalism L2 Formal Series Bounds FBChart ex lg at  f2d449f095ce
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds FBChart ex lg at  f2d449f095ce construction uses the P2 M Formalism L2 Formal Series Bounds FBChart ex lg at  f2d449f095ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean#L31-L37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstVanishingAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLinearCombination
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem P2M_Formalism_L2_FormalSeriesBounds_FBChart_ex_lg_at__f2d449f095ce (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«FBChart».«ex_lg_at'» := P2M_Formalism_L2_FormalSeriesBounds_FBChart_ex_lg_at__f2d449f095ce
