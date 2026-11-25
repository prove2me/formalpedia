-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_VP_subst_sub__6279a8cf8e49
-- name    : P2M_Formalism_L2_FormalSeriesBounds_VP_subst_sub__6279a8cf8e49
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:03.643734+00:00
-- url     : https://prove2.me/theorems/58166ea4-6ba7-5e36-b10d-a03667e9662a
-- title:
--   P2 M Formalism L2 Formal Series Bounds VP subst sub  6279a8cf8e49: P2 M Formalism L2 Formal Series Bounds VP subst sub  6279a8cf8e49
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds VP subst sub  6279a8cf8e49 construction uses the P2 M Formalism L2 Formal Series Bounds VP subst sub  6279a8cf8e49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L48-L52

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

theorem P2M_Formalism_L2_FormalSeriesBounds_VP_subst_sub__6279a8cf8e49 {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f - g) = MvPowerSeries.subst a f - MvPowerSeries.subst a g := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«VP».«subst_sub'» := P2M_Formalism_L2_FormalSeriesBounds_VP_subst_sub__6279a8cf8e49
