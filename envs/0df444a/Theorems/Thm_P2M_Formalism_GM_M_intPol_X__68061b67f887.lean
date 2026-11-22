-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_X__68061b67f887
-- name    : P2M_Formalism_GM_M_intPol_X__68061b67f887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:05.560548+00:00
-- url     : https://prove2.me/theorems/b25bf4a1-0035-48fd-9278-28909c0bd129
-- title:
--   P2 M Formalism GM M int Pol X  68061b67f887: P2 M Formalism GM M int Pol X  68061b67f887
-- statement:
--   The P2 M Formalism GM M int Pol X  68061b67f887 construction uses the P2 M Formalism GM M int Pol X  68061b67f887 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L502-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L502-L503

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

theorem P2M_Formalism_GM_M_intPol_X__68061b67f887 (x : σ) : (X x : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_X'» := P2M_Formalism_GM_M_intPol_X__68061b67f887
