-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_rename__d2058bf01e91
-- name    : P2M_Formalism_GM_M_intPol_rename__d2058bf01e91
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:12.013821+00:00
-- url     : https://prove2.me/theorems/2e22ff62-c611-4e12-ab18-d4c203371f51
-- title:
--   P2 M Formalism GM M int Pol rename  d2058bf01e91: P2 M Formalism GM M int Pol rename  d2058bf01e91
-- statement:
--   The P2 M Formalism GM M int Pol rename  d2058bf01e91 construction uses the P2 M Formalism GM M int Pol rename  d2058bf01e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L521-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L521-L524

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

theorem P2M_Formalism_GM_M_intPol_rename__d2058bf01e91 {τ : Type} (e : τ → σ) {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    rename e y ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_rename'» := P2M_Formalism_GM_M_intPol_rename__d2058bf01e91
