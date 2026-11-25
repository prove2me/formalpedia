-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc
-- name    : P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:25.180524+00:00
-- url     : https://prove2.me/theorems/0f3be657-2ff8-4605-b2c9-f9cd98af8d78
-- title:
--   P2 M Formalism LFunction Chain Parameters Weighted Mean Lemmas wmean mono  ee8853d08dcc: P2 M Formalism LFunction Chain Parameters Weighted Mean Lemmas wmean mono  ee8853d08dcc
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Weighted Mean Lemmas wmean mono  ee8853d08dcc construction uses the P2 M Formalism LFunction Chain Parameters Weighted Mean Lemmas wmean mono  ee8853d08dcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedMeanLemmaNeedsDegree.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedMeanLemmaNeedsDegree.lean#L16-L21

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
variable {ι : Type*} [Fintype ι]

theorem P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ u, 0 < d u)
    (hXY : ∀ u, X u ≤ Y u) : wmean d X ≤ wmean d Y := by sorry

alias «Formalism».«LFunctionChainParameters».«WeightedMeanLemmas».«wmean_mono'» := P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc
