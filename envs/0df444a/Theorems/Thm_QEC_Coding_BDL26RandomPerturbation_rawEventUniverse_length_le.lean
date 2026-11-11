-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_rawEventUniverse_length_le
-- name    : QEC.Coding.BDL26RandomPerturbation.rawEventUniverse_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:53:41.851215+00:00
-- url     : https://prove2.me/theorems/0c60a80b-0798-4d50-ad6a-b40ee82b8030
-- title:
--   BDL26 Random Perturbation: raw Event Universe length le
-- statement:
--   The BDL26 Random Perturbation construction uses the raw Event Universe length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L36-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L36-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.rawEventUniverse_length_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : (rawEventUniverseQuery P J hr).1.length ≤ Fintype.card (Triangle P)^4 := by sorry
