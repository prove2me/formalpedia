-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e
-- name    : P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:09.499064+00:00
-- url     : https://prove2.me/theorems/9cd8f42c-ae43-446f-9b73-8f32e7187654
-- title:
--   P2 M Formalism GM M Phi Integrality pderiv comm  350abda6d36e: P2 M Formalism GM M Phi Integrality pderiv comm  350abda6d36e
-- statement:
--   The P2 M Formalism GM M Phi Integrality pderiv comm  350abda6d36e construction uses the P2 M Formalism GM M Phi Integrality pderiv comm  350abda6d36e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L83-L93

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e (i j : σ) (f : MvPolynomial σ ℚ_[p]) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by sorry

alias «Formalism».«GM».«M».«PhiIntegrality».«pderiv_comm'» := P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e
