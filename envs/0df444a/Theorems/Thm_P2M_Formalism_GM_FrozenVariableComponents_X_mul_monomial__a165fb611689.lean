-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689
-- name    : P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:52.704132+00:00
-- url     : https://prove2.me/theorems/1fe60956-720f-4784-8114-7e0d343c8a45
-- title:
--   P2 M Formalism GM Frozen Variable Components X mul monomial  a165fb611689: P2 M Formalism GM Frozen Variable Components X mul monomial  a165fb611689
-- statement:
--   The P2 M Formalism GM Frozen Variable Components X mul monomial  a165fb611689 construction uses the P2 M Formalism GM Frozen Variable Components X mul monomial  a165fb611689 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L164-L167

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

theorem P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689 {σ : Type*} (x : σ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) * monomial m a = monomial (m + Finsupp.single x 1) a := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«X_mul_monomial'» := P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689
