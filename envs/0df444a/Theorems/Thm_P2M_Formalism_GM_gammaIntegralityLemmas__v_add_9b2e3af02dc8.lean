-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:31.426274+00:00
-- url     : https://prove2.me/theorems/0d4d6cc6-c344-4c27-a338-6b11711164ff
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas  v add 9b2e3af02dc8: P2 M Formalism GM gamma Integrality Lemmas  v add 9b2e3af02dc8
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas  v add 9b2e3af02dc8 construction uses the P2 M Formalism GM gamma Integrality Lemmas  v add 9b2e3af02dc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L758-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L758-L759

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}

theorem P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8 (β β' : Fin (N + 1 + 1) × Fin r →₀ ℕ) : δv (β + β') = δv β + δv β' := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«δv_add» := P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
