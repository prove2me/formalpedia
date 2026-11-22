-- Prove2me | Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc
-- name    : P2M_Formalism_GM_tieE_apply__373a5b0b31bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:52.270331+00:00
-- url     : https://prove2.me/theorems/517705bf-468f-42ca-adbf-74ab5cf27d12
-- title:
--   P2 M Formalism GM tie E apply  373a5b0b31bc: P2 M Formalism GM tie E apply  373a5b0b31bc
-- statement:
--   The P2 M Formalism GM tie E apply  373a5b0b31bc construction uses the P2 M Formalism GM tie E apply  373a5b0b31bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L10-L12

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

theorem P2M_Formalism_GM_tieE_apply__373a5b0b31bc (g : MvPolynomial σ k) :
    tieE w e g = (∑ c, X (w c) * X (e c)) * g := by sorry

alias «Formalism».«GM».«tieE_apply'» := P2M_Formalism_GM_tieE_apply__373a5b0b31bc
