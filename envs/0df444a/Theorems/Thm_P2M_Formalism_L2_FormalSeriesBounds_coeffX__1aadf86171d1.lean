-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_coeffX__1aadf86171d1
-- name    : P2M_Formalism_L2_FormalSeriesBounds_coeffX__1aadf86171d1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:09.417285+00:00
-- url     : https://prove2.me/theorems/9abbb77f-b314-5013-b253-34ca44f0d6a1
-- title:
--   P2 M Formalism L2 Formal Series Bounds coeff X  1aadf86171d1: P2 M Formalism L2 Formal Series Bounds coeff X  1aadf86171d1
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds coeff X  1aadf86171d1 construction uses the P2 M Formalism L2 Formal Series Bounds coeff X  1aadf86171d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L184-L185

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem P2M_Formalism_L2_FormalSeriesBounds_coeffX__1aadf86171d1 (n : ℕ) : PowerSeries.coeff n (MvPowerSeries.X () : PowerSeries C) = if n = 1 then 1 else 0 := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«coeffX'» := P2M_Formalism_L2_FormalSeriesBounds_coeffX__1aadf86171d1
