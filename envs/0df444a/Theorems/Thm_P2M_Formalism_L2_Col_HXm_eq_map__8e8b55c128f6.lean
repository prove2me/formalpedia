-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Col_HXm_eq_map__8e8b55c128f6
-- name    : P2M_Formalism_L2_Col_HXm_eq_map__8e8b55c128f6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:16:50.568869+00:00
-- url     : https://prove2.me/theorems/10325c77-951e-4c15-80c6-ec79aa5ba285
-- title:
--   P2 M Formalism L2 Col HXm eq map  8e8b55c128f6: P2 M Formalism L2 Col HXm eq map  8e8b55c128f6
-- statement:
--   The P2 M Formalism L2 Col HXm eq map  8e8b55c128f6 construction uses the P2 M Formalism L2 Col HXm eq map  8e8b55c128f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L927-L930
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L927-L930

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem P2M_Formalism_L2_Col_HXm_eq_map__8e8b55c128f6 (n' r t m : ℕ) (hn : n' = r + m * t) :
    HXm κ (n' + 1) r t m = (HJ κ n' r t m).map (diagEmb κ (Nat.le_succ n')) := by sorry

alias «Formalism».«L2».«Col».«HXm_eq_map'» := P2M_Formalism_L2_Col_HXm_eq_map__8e8b55c128f6
