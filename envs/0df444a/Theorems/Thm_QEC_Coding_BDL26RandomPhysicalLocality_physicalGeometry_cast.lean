-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_cast
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.physicalGeometry_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:54.919392+00:00
-- url     : https://prove2.me/theorems/81c916aa-c312-410b-8794-921656e2fb51
-- title:
--   BDL26 Random Physical Locality: physical Geometry cast
-- statement:
--   Reindex a physical map along an actual level equality, retaining all labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L138-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L138-L143

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPhysicalLocality.physicalGeometry_cast (S : OddScale) (m n : Nat) (h : m = n)
    (J : Vertex (state S m).presentation → E) (t : ℝ) (hg : PhysicalGeometry S m J t) :
    PhysicalGeometry S n
      (fun v => J (cast (congrArg (fun a => Vertex (state S a).presentation) h.symm) v)) t := by sorry
