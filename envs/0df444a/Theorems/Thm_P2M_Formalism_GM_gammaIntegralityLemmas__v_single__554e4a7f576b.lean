-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:35.867525+00:00
-- url     : https://prove2.me/theorems/93ba9825-2c70-40ee-a4a8-19f0ad3f0cd0
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas  v single  554e4a7f576b: P2 M Formalism GM gamma Integrality Lemmas  v single  554e4a7f576b
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas  v single  554e4a7f576b construction uses the P2 M Formalism GM gamma Integrality Lemmas  v single  554e4a7f576b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1079-L1085
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1079-L1085

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

theorem P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b (a : Fin (N + 1 + 1)) (c : Fin r) (t : ℕ) :
    δv (Finsupp.single (a, c) t) = Pi.single a t := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«δv_single'» := P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b
