-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_faceZ_surjective
-- name    : QEC.Coding.BDL26RandomPerturbation.faceZ_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:24.20169+00:00
-- url     : https://prove2.me/theorems/dcc6bdeb-9ae1-465e-9e33-aec53e2ef8ae
-- title:
--   BDL26 Random Perturbation: face Z surjective
-- statement:
--   The BDL26 Random Perturbation construction uses the face Z surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L29-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L29-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RandomPerturbation.faceZ_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective P.faceZ := by sorry
