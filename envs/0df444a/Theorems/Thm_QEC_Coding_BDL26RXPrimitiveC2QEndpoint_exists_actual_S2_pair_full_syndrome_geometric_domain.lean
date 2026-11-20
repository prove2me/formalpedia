-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_exists_actual_S2_pair_full_syndrome_geometric_domain
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_actual_S2_pair_full_syndrome_geometric_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:37:08.895269+00:00
-- url     : https://prove2.me/theorems/1d702bab-a29a-41eb-b6cd-5577c1ba6369
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: exists actual S2 pair full syndrome geometric domain
-- statement:
--   For every OddScale, one SAME actual S2 error and its SAME full actual
--   syndrome have exact supports inside one genuine closed X-star. The explicit
--   G3 and canonical-owner G2 geometric conclusions keep their carriers separate.
--   The error is outside current F17 owner-fibre locality; the syndrome owners
--   fit an undirected one-edge G2 ball but no directed incoming radius-two ball.
--   No decoder-correctability, paper-domain or large-scale-distance claim follows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L19021-L19072
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L19021-L19072

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
set_option autoImplicit false
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout
open scoped Classical

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_actual_S2_pair_full_syndrome_geometric_domain (S : OddScale) :
    ∃ x : (state S 2).presentation.X,
      ∃ qr qb : (state S 2).presentation.Q,
      ∃ za zb : (state S 2).presentation.Z,
      ∃ oldq : (state S 1).presentation.Q,
        let e : Word BDL26Field (state S 2).presentation.Q :=
          canonicalBasisWord qr+canonicalBasisWord qb
        let sigma : Word BDL26Field (state S 2).presentation.Z :=
          QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S 2).presentation e
        qr≠qb ∧ za≠zb ∧ hammingSupport e={qr,qb} ∧
        hammingSupport sigma={za,zb} ∧
        (∃ f : (state S 2).presentation.Face, ∃ c : BDL26FiniteTannerSquare.Two,
          (state S 2).presentation.faceX f=x ∧
          (state S 2).presentation.faceQ f c=qr ∧
          (state S 2).presentation.faceQ f (if c=0 then 1 else 0)=qb) ∧
        (∀ q ∈ hammingSupport e,
          xStarVertexMember (state S 2).presentation x (.q q)=true ∧
          (level S 3).skeleton.adjacent (.x x) (.q q)) ∧
        (∀ z ∈ hammingSupport sigma,
          xStarVertexMember (state S 2).presentation x (.z z)=true ∧
          (level S 3).graph.reachableWithin 2 (.x x) (.z z)=true) ∧
        (∀ z ∈ hammingSupport sigma,
          (level S 2).skeleton.adjacent (.q oldq)
            (BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z)) ∧
        ¬ BDL26LevelTwoDistance.levelTwoLocalError S e ∧
        (¬ ∃ center : GraphVertex S 2,
          ∀ z ∈ hammingSupport sigma,
            BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z=center) ∧
        (¬ ∃ center : GraphVertex S 2,
          ∀ z ∈ hammingSupport sigma,
            BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z ∈
              LocalRegion.directedNeighborhood (level S 2).graph center 2) := by sorry
