-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_VP_subst_zero__0bce5ca5ae89
-- name    : P2M_Formalism_L2_FormalSeriesBounds_VP_subst_zero__0bce5ca5ae89
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:58:00.573954+00:00
-- url     : https://prove2.me/theorems/dbe50752-3ecd-5863-88ba-0e90da9143aa
-- title:
--   P2 M Formalism L2 Formal Series Bounds VP subst zero  0bce5ca5ae89: P2 M Formalism L2 Formal Series Bounds VP subst zero  0bce5ca5ae89
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds VP subst zero  0bce5ca5ae89 construction uses the P2 M Formalism L2 Formal Series Bounds VP subst zero  0bce5ca5ae89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L39-L41

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem P2M_Formalism_L2_FormalSeriesBounds_VP_subst_zero__0bce5ca5ae89 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«VP».«subst_zero'» := P2M_Formalism_L2_FormalSeriesBounds_VP_subst_zero__0bce5ca5ae89
