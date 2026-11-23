-- Prove2me | Theorems.Thm_P2M_Formalism_REAL_root_swap__b8b06e6cdac5
-- name    : P2M_Formalism_REAL_root_swap__b8b06e6cdac5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:00.175848+00:00
-- url     : https://prove2.me/theorems/e4d677e4-2c7c-4a04-9604-a9e1cf1ee1b0
-- title:
--   P2 M Formalism REAL root swap  b8b06e6cdac5: P2 M Formalism REAL root swap  b8b06e6cdac5
-- statement:
--   The P2 M Formalism REAL root swap  b8b06e6cdac5 construction uses the P2 M Formalism REAL root swap  b8b06e6cdac5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L318-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L318-L319

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem P2M_Formalism_REAL_root_swap__b8b06e6cdac5 {n : ℕ} (a b : Fin n) : root a b = -root b a := by sorry

alias «Formalism».«REAL».«root_swap'» := P2M_Formalism_REAL_root_swap__b8b06e6cdac5
