-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_VP_subst_pow__05906f14b766
-- name    : P2M_Formalism_L2_FormalSeriesBounds_VP_subst_pow__05906f14b766
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:31.531078+00:00
-- url     : https://prove2.me/theorems/59a2fd9d-0a39-4449-82fd-532841d16ca0
-- title:
--   P2 M Formalism L2 Formal Series Bounds VP subst pow  05906f14b766: P2 M Formalism L2 Formal Series Bounds VP subst pow  05906f14b766
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds VP subst pow  05906f14b766 construction uses the P2 M Formalism L2 Formal Series Bounds VP subst pow  05906f14b766 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L57-L63

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

theorem P2M_Formalism_L2_FormalSeriesBounds_VP_subst_pow__05906f14b766 {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (k : ℕ) :
    MvPowerSeries.subst a (f ^ k) = MvPowerSeries.subst a f ^ k := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«VP».«subst_pow'» := P2M_Formalism_L2_FormalSeriesBounds_VP_subst_pow__05906f14b766
