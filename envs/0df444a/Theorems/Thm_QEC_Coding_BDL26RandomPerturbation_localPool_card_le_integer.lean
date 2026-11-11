-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_card_le_integer
-- name    : QEC.Coding.BDL26RandomPerturbation.localPool_card_le_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:15:40.098002+00:00
-- url     : https://prove2.me/theorems/25db1a12-0f10-4c87-8fd4-78d26323104a
-- title:
--   BDL26 Random Perturbation: local Pool card le integer
-- statement:
--   The BDL26 Random Perturbation construction uses the local Pool card le integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L78-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L78-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.localPool_card_le_integer (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K M : ℕ)
    (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ)) (a : Triangle P) :
    (localPool P J K a).card ≤ M := by sorry
