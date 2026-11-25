-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:22.878929+00:00
-- url     : https://prove2.me/theorems/d309fd03-e42b-49c1-90df-99da0d613d89
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff coeff   2f0e7d943746: P2 M Formalism GM Frozen Variable Components coeff coeff   2f0e7d943746
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff coeff   2f0e7d943746 construction uses the P2 M Formalism GM Frozen Variable Components coeff coeff   2f0e7d943746 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L149-L151

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
variable {K : Type*} [CommRing K] {N r : ℕ}

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746 (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff m (coeffη b F) = coeff (comb b m) F := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeff_coeffη'» := P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746
