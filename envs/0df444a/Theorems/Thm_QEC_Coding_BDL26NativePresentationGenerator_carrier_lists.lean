-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_carrier_lists
-- name    : QEC.Coding.BDL26NativePresentationGenerator.carrier_lists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:46:03.449112+00:00
-- url     : https://prove2.me/theorems/721da773-b47e-490d-8243-26a2c4c24f0f
-- title:
--   BDL26 Native Presentation Generator: carrier lists
-- statement:
--   Nodup and full metadata/list consistency are established by actual generation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3114-L3119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3114-L3119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.carrier_lists (S : OddScale) (n : ℕ) :
    let F := (generateQ S n).1
    F.xs.length=F.nx ∧ F.qs.length=F.nq ∧ F.zs.length=F.nz ∧ F.faces.length=F.nf ∧
      F.xs.Nodup ∧ F.qs.Nodup ∧ F.zs.Nodup ∧ (F.faces.map FaceRow.code).Nodup := by sorry
