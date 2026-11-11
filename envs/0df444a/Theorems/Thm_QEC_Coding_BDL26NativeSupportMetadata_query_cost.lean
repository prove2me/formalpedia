-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:46:35.374952+00:00
-- url     : https://prove2.me/theorems/90dab306-011b-4ef1-9496-797dcec88c43
-- title:
--   BDL26 Native Support Metadata: query cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L363-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L363-L399

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N

theorem QEC.Coding.BDL26NativeSupportMetadata.query_cost (S : OddScale) (n : ℕ) (codes : FourCodes) :
    (queryQ S n codes).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(44*(T S n).length+2*(F S n).faces.length+132*(V S n).length+50)+
      172*(T S n).length+400 ∧
    (queryQ S n codes).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+8)+26 := by sorry
