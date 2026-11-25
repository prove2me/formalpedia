-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_prod__f889d80e71c9
-- name    : P2M_Formalism_GM_M_intPol_prod__f889d80e71c9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:35.665906+00:00
-- url     : https://prove2.me/theorems/e3bbd307-4ebb-486c-84df-88f5e5009177
-- title:
--   P2 M Formalism GM M int Pol prod  f889d80e71c9: P2 M Formalism GM M int Pol prod  f889d80e71c9
-- statement:
--   The P2 M Formalism GM M int Pol prod  f889d80e71c9 construction uses the P2 M Formalism GM M int Pol prod  f889d80e71c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L512-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L512-L519

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

theorem P2M_Formalism_GM_M_intPol_prod__f889d80e71c9 {α : Type} (u : Finset α) (f : α → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ u, f i ∈ IntPol p σ) :
    (∏ i ∈ u, f i) ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_prod'» := P2M_Formalism_GM_M_intPol_prod__f889d80e71c9
