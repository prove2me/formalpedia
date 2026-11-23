-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:31.386952+00:00
-- url     : https://prove2.me/theorems/3ba48e27-7d25-4e60-8427-6d776f0728c1
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas le  v d8c333cc96ac: P2 M Formalism GM gamma Integrality Lemmas le  v d8c333cc96ac
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas le  v d8c333cc96ac construction uses the P2 M Formalism GM gamma Integrality Lemmas le  v d8c333cc96ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1090-L1091
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1090-L1091

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

theorem P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) (i : Fin (N + 1 + 1)) (c : Fin r) : β (i, c) ≤ δv β i := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«le_δv» := P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac
