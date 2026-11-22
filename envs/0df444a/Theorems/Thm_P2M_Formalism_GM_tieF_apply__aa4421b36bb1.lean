-- Prove2me | Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1
-- name    : P2M_Formalism_GM_tieF_apply__aa4421b36bb1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:43:02.674829+00:00
-- url     : https://prove2.me/theorems/3ef5cb29-dc3a-4182-8ff5-b099898ff74c
-- title:
--   P2 M Formalism GM tie F apply  aa4421b36bb1: P2 M Formalism GM tie F apply  aa4421b36bb1
-- statement:
--   The P2 M Formalism GM tie F apply  aa4421b36bb1 construction uses the P2 M Formalism GM tie F apply  aa4421b36bb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L14-L16

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

theorem P2M_Formalism_GM_tieF_apply__aa4421b36bb1 (g : MvPolynomial σ k) :
    tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by sorry

alias «Formalism».«GM».«tieF_apply'» := P2M_Formalism_GM_tieF_apply__aa4421b36bb1
