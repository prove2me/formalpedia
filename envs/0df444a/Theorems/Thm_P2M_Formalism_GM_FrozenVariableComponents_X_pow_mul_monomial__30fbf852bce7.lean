-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7
-- name    : P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:15.605685+00:00
-- url     : https://prove2.me/theorems/60e9f2e6-1f53-4ff9-9eac-206c1ed10587
-- title:
--   P2 M Formalism GM Frozen Variable Components X pow mul monomial  30fbf852bce7: P2 M Formalism GM Frozen Variable Components X pow mul monomial  30fbf852bce7
-- statement:
--   The P2 M Formalism GM Frozen Variable Components X pow mul monomial  30fbf852bce7 construction uses the P2 M Formalism GM Frozen Variable Components X pow mul monomial  30fbf852bce7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L169-L171

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

theorem P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7 {σ : Type*} (x : σ) (k : ℕ) (m : σ →₀ ℕ) (a : K) :
    (X x : MvPolynomial σ K) ^ k * monomial m a = monomial (m + Finsupp.single x k) a := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«X_pow_mul_monomial'» := P2M_Formalism_GM_FrozenVariableComponents_X_pow_mul_monomial__30fbf852bce7
