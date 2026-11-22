-- Prove2me | Theorems.Thm_P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da
-- name    : P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:46:18.960406+00:00
-- url     : https://prove2.me/theorems/f74d9a97-d3e9-412f-aadd-d870dc7c4961
-- title:
--   P2 M Formalism GM coeff X mul pderiv  a9db2daf30da: P2 M Formalism GM coeff X mul pderiv  a9db2daf30da
-- statement:
--   The P2 M Formalism GM coeff X mul pderiv  a9db2daf30da construction uses the P2 M Formalism GM coeff X mul pderiv  a9db2daf30da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L18-L42

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)

theorem P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da (i : σ) (p : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i p) = coeff m p * (m i : k) := by sorry

alias «Formalism».«GM».«coeff_X_mul_pderiv'» := P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da
