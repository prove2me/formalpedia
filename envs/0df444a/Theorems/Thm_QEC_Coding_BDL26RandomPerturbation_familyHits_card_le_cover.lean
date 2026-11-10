-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_familyHits_card_le_cover
-- name    : QEC.Coding.BDL26RandomPerturbation.familyHits_card_le_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:45:02.715857+00:00
-- url     : https://prove2.me/theorems/a6342fac-5687-4532-bd40-576933cce51c
-- title:
--   BDL26 Random Perturbation: family Hits card le cover
-- statement:
--   Covering counts preserve labels, including coincident or collapsed images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L11-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L11-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.familyHits_card_le_cover {ι κ E : Type*} [Fintype ι] [Fintype κ]
    (images : ι → Set E) (region : Set E) (cover : κ → Set E)
    (hcover : ∀ p ∈ region, ∃ k, p ∈ cover k) :
    (familyHits images region).card ≤ ∑ k, (familyHits images (cover k)).card := by sorry
