-- Prove2me | Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
-- name    : P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:33.617489+00:00
-- url     : https://prove2.me/theorems/df76c9cd-bbd0-47bf-9107-bce0d7485205
-- title:
--   P2 M Formalism GM leading Term Lemmas bi Hom sq  c19e50466e6a: P2 M Formalism GM leading Term Lemmas bi Hom sq  c19e50466e6a
-- statement:
--   The P2 M Formalism GM leading Term Lemmas bi Hom sq  c19e50466e6a construction uses the P2 M Formalism GM leading Term Lemmas bi Hom sq  c19e50466e6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L940-L952
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L940-L952

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

theorem P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - m (Fin.last N, ρ)) (LL.total - m (Fin.last N, ρ))
      (sq (K := K) LL ρ m) := by sorry

alias «Formalism».«GM».«leadingTermLemmas».«biHom_sq'» := P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
