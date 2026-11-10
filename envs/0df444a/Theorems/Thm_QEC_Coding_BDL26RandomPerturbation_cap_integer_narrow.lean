-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_cap_integer_narrow
-- name    : QEC.Coding.BDL26RandomPerturbation.cap_integer_narrow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:49:57.346736+00:00
-- url     : https://prove2.me/theorems/c8f79d5d-80f0-4c96-b1cd-763e51df53e4
-- title:
--   BDL26 Random Perturbation: cap integer narrow
-- statement:
--   Narrowness follows from the selected integer cap parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L56-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L56-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.cap_integer_narrow {m : ℕ} (hm : 2 ≤ m) :
    0 < (1 : ℝ)/(12*m) ∧ (1 : ℝ)/(12*m) ≤ 1/24 := by sorry
