-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:20.887452+00:00
-- url     : https://prove2.me/theorems/ee783e7d-f230-403b-96b7-d7fede813b47
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas fock def  dcd241737a4a: P2 M Formalism GM gamma Integrality Lemmas fock def  dcd241737a4a
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas fock def  dcd241737a4a construction uses the P2 M Formalism GM gamma Integrality Lemmas fock def  dcd241737a4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L299-L302

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
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * wf m := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«fock_def'» := P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
