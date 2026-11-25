-- Prove2me | Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad
-- name    : P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:21.057397+00:00
-- url     : https://prove2.me/theorems/f4d279ea-af8e-4d81-bc04-1fa84b154f88
-- title:
--   P2 M Formalism GM leading Term Lemmas choose lim  68d426c4c0ad: P2 M Formalism GM leading Term Lemmas choose lim  68d426c4c0ad
-- statement:
--   The P2 M Formalism GM leading Term Lemmas choose lim  68d426c4c0ad construction uses the P2 M Formalism GM leading Term Lemmas choose lim  68d426c4c0ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1226-L1239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1226-L1239

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset

theorem P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad (S j d : ℕ) (hjd : j ≤ d) :
    Tendsto (fun n : ℕ => ((n + j - S).choose j : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (if j = d then 1 / (d.factorial : ℝ) else 0)) := by sorry

alias «Formalism».«GM».«leadingTermLemmas».«choose_lim'» := P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad
