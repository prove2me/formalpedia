-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_faceX_surjective
-- name    : QEC.Coding.BDL26RandomPerturbation.faceX_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:11.82035+00:00
-- url     : https://prove2.me/theorems/3b8021af-5893-4d97-8240-5c7aedf602aa
-- title:
--   BDL26 Random Perturbation: face X surjective
-- statement:
--   An actual X-star boundary root supplies a face, even without a chosen edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L14-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L14-L27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RandomPerturbation.faceX_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective P.faceX := by sorry
