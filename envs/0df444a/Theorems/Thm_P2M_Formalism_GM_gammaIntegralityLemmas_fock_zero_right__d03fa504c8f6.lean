-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:36.3582+00:00
-- url     : https://prove2.me/theorems/c68e172e-4ab6-43ba-b94f-def5d0dd5bf7
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas fock zero right  d03fa504c8f6: P2 M Formalism GM gamma Integrality Lemmas fock zero right  d03fa504c8f6
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas fock zero right  d03fa504c8f6 construction uses the P2 M Formalism GM gamma Integrality Lemmas fock zero right  d03fa504c8f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1131-L1133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1131-L1133

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

theorem P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6 {σ : Type} [Fintype σ] [DecidableEq σ] (F : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F 0 = 0 := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«fock_zero_right'» := P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6
