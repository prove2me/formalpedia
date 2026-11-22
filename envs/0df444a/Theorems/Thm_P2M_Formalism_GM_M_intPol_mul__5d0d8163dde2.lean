-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
-- name    : P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:53.378799+00:00
-- url     : https://prove2.me/theorems/9f7f089d-f766-4e80-9e86-de8e83a5e068
-- title:
--   P2 M Formalism GM M int Pol mul  5d0d8163dde2: P2 M Formalism GM M int Pol mul  5d0d8163dde2
-- statement:
--   The P2 M Formalism GM M int Pol mul  5d0d8163dde2 construction uses the P2 M Formalism GM M int Pol mul  5d0d8163dde2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L496-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L496-L500

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {σ : Type}

theorem P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2 {F G : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (hG : G ∈ IntPol p σ) :
    F * G ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_mul'» := P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
