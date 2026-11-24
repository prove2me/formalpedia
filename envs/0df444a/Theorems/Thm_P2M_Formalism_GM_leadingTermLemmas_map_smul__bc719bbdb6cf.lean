-- Prove2me | Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_map_smul__bc719bbdb6cf
-- name    : P2M_Formalism_GM_leadingTermLemmas_map_smul__bc719bbdb6cf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:41.002088+00:00
-- url     : https://prove2.me/theorems/244dd1f4-f357-420d-a9b8-e87352ff2c41
-- title:
--   P2 M Formalism GM leading Term Lemmas map smul  bc719bbdb6cf: P2 M Formalism GM leading Term Lemmas map smul  bc719bbdb6cf
-- statement:
--   The P2 M Formalism GM leading Term Lemmas map smul  bc719bbdb6cf construction uses the P2 M Formalism GM leading Term Lemmas map smul  bc719bbdb6cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1765-L1766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1765-L1766

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
open MvPolynomial Finset Formalism.GM
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem P2M_Formalism_GM_leadingTermLemmas_map_smul__bc719bbdb6cf (c : ℚ) (g : MvPolynomial σ ℚ) : map ι (c • g) = (ι c) • map ι g := by sorry

alias «Formalism».«GM».«leadingTermLemmas».«map_smul'» := P2M_Formalism_GM_leadingTermLemmas_map_smul__bc719bbdb6cf
