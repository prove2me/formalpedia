-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50
-- name    : P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:52.218466+00:00
-- url     : https://prove2.me/theorems/d1b7d94a-664d-4b5f-971c-2079311e5a37
-- title:
--   P2 M Formalism GM M int Pol iff  d65ab3cebd50: P2 M Formalism GM M int Pol iff  d65ab3cebd50
-- statement:
--   The P2 M Formalism GM M int Pol iff  d65ab3cebd50 construction uses the P2 M Formalism GM M int Pol iff  d65ab3cebd50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L492-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L492-L494

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

theorem P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50 (F : MvPolynomial σ ℚ_[p]) :
    F ∈ IntPol p σ ↔ ∃ F₀ : MvPolynomial σ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by sorry

alias «Formalism».«GM».«M».«intPol_iff'» := P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50
