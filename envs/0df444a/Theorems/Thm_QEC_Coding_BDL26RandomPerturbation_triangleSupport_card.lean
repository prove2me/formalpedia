-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleSupport_card
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleSupport_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:42:17.953309+00:00
-- url     : https://prove2.me/theorems/82c00844-0cc6-46a8-a347-6a5c7eebb447
-- title:
--   BDL26 Random Perturbation: triangle Support card
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Support card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L42-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L42-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding

theorem QEC.Coding.BDL26RandomPerturbation.triangleSupport_card (P : TannerSquarePresentation) (t : Triangle P) :
    (triangleSupport P t).card = 3 := by sorry
