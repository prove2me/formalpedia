-- Prove2me | Theorems.Thm_P2M_Formalism_GM_GammaExpansion_pderiv_comm__f76eb5955bec
-- name    : P2M_Formalism_GM_GammaExpansion_pderiv_comm__f76eb5955bec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:51.790818+00:00
-- url     : https://prove2.me/theorems/9b379cf1-1c11-41b5-ac67-a448a58a952f
-- title:
--   P2 M Formalism GM Gamma Expansion pderiv comm  f76eb5955bec: P2 M Formalism GM Gamma Expansion pderiv comm  f76eb5955bec
-- statement:
--   The P2 M Formalism GM Gamma Expansion pderiv comm  f76eb5955bec construction uses the P2 M Formalism GM Gamma Expansion pderiv comm  f76eb5955bec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L12-L22

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]

theorem P2M_Formalism_GM_GammaExpansion_pderiv_comm__f76eb5955bec (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by sorry

alias «Formalism».«GM».«GammaExpansion».«pderiv_comm'» := P2M_Formalism_GM_GammaExpansion_pderiv_comm__f76eb5955bec
