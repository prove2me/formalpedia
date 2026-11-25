-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_pow__7258d14ed956
-- name    : P2M_Formalism_GM_M_intPol_pow__7258d14ed956
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:37.954565+00:00
-- url     : https://prove2.me/theorems/149c2f11-dfe8-4882-843e-e47b754cad01
-- title:
--   P2 M Formalism GM M int Pol pow  7258d14ed956: P2 M Formalism GM M int Pol pow  7258d14ed956
-- statement:
--   The P2 M Formalism GM M int Pol pow  7258d14ed956 construction uses the P2 M Formalism GM M int Pol pow  7258d14ed956 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L508-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L508-L510

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

theorem P2M_Formalism_GM_M_intPol_pow__7258d14ed956 {F : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (k : ℕ) : F ^ k ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_pow'» := P2M_Formalism_GM_M_intPol_pow__7258d14ed956
