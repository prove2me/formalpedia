-- Prove2me | Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
-- name    : P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:49.777366+00:00
-- url     : https://prove2.me/theorems/e43ad0e4-af0e-4038-85fb-97c5c840f1f8
-- title:
--   P2 M Formalism GM leading Term Lemmas e  inj b83b9739b71a: P2 M Formalism GM leading Term Lemmas e  inj b83b9739b71a
-- statement:
--   The P2 M Formalism GM leading Term Lemmas e  inj b83b9739b71a construction uses the P2 M Formalism GM leading Term Lemmas e  inj b83b9739b71a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L828-L828
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L828-L828

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a : Function.Injective (eη (N := N) (r := r)) := by sorry

alias «Formalism».«GM».«leadingTermLemmas».«eη_inj» := P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
