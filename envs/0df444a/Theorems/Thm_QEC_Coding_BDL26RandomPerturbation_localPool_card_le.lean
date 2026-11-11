-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.localPool_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:04:03.376733+00:00
-- url     : https://prove2.me/theorems/0bb0f418-5ea6-43ab-ad5d-c921786df458
-- title:
--   BDL26 Random Perturbation: local Pool card le
-- statement:
--   Cover counts bound the local pool independently of the perturbation scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L68-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L68-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.localPool_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K : ℕ) (a : Triangle P) :
    ((localPool P J K a).card : ℝ) ≤ (2*K+1 : ℕ)^3*(250*t) := by sorry
