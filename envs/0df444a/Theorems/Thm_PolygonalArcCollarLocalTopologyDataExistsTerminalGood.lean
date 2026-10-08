-- Prove2me | Theorems.Thm_PolygonalArcCollarLocalTopologyDataExistsTerminalGood
-- name    : PolygonalArcCollarLocalTopologyDataExistsTerminalGood
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T22:29:48.826348+00:00
-- url     : https://prove2.me/theorems/447a419f-ad75-48aa-8e1c-a9739076395c
-- title:
--   Polygonal Arc Collar Local Topology Data Exists Terminal Good
-- statement:
--   Auxiliary lemma split out of the Lean proof of the node `PolygonalArcCollarLocalTopologyDataExists` of the Trellis formalization: it is the intermediate claim `hGoodTerminal` of that proof, stated with the local facts established earlier in the proof as hypotheses (elementary properties of the affine chart $z\mapsto p+z_0 d+z_1\,\mathrm{rot}_{90}(d)$, closure statements for the model wedges and discs, and the neighbourhood-disjointness facts from the collar data) followed by the local definitions used there. The split keeps each verification job below the platform's compile-time limit.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the intermediate claim comes from the proof of the Trellis node `PolygonalArcCollarLocalTopologyDataExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalTopologyDataExists.lean#L1-L2645

import Definitions.Def_PolygonalArcCollarLocalTopologyData
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData
import Definitions.Def_PolygonalArcCollarVertexLocalPieceData

open Classical
noncomputable section

theorem PolygonalArcCollarLocalTopologyDataExistsTerminalGood (γ : PolygonalArc) {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η) (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments forbiddenMargins) (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments forbiddenMargins compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData) :
  let sep : PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments forbiddenMargins := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData;
  let E : Type := EuclideanSpace ℝ (Fin 2);
  (chart_image_open : ∀ (p d : E), d ≠ 0 → ∀ (S : Set E), IsOpen S → IsOpen ((fun (z : E) => p + z.ofLp 0 • d + z.ofLp 1 • PlanarRot90 d) '' S)) →
  (chart_injective : ∀ (p d : E), d ≠ 0 → Function.Injective fun (z : E) => p + z.ofLp 0 • d + z.ofLp 1 • PlanarRot90 d) →
  (chart_continuous : ∀ (p d : E), Continuous fun (z : E) => p + z.ofLp 0 • d + z.ofLp 1 • PlanarRot90 d) →
  (chart_mem_closure_image : ∀ (p d : E) {S : Set E} {z : E}, z ∈ closure S → p + z.ofLp 0 • d + z.ofLp 1 • PlanarRot90 d ∈ closure ((fun (z : E) => p + z.ofLp 0 • d + z.ofLp 1 • PlanarRot90 d) '' S)) →
  (ray_mem_closure : ∀ (a : ℝ) {S : Set E} {x w : E}, x ∈ Metric.ball 0 a → (∃ (μ : ℝ), 0 < μ ∧ ∀ (δ : ℝ), 0 < δ → δ < μ → x + δ • w ∈ Metric.ball 0 a → x + δ • w ∈ S) → x ∈ closure S) →
  (endpoint_germ_subset_closure_left : ∀ (a K : ℝ), 0 < a → 0 < K → let L : Set E := {z : E | 0 < z.ofLp 0 ∧ z.ofLp 0 ^ 2 + z.ofLp 1 ^ 2 < a ^ 2 ∧ 0 < z.ofLp 1 ∧ z.ofLp 1 < K * z.ofLp 0}; let G : Set E := {z : E | 0 < z.ofLp 0 ∧ z.ofLp 0 < a ∧ z.ofLp 1 = 0}; G ⊆ closure L) →
  (endpoint_germ_subset_closure_right : ∀ (a K : ℝ), 0 < a → 0 < K → let R : Set E := {z : E | 0 < z.ofLp 0 ∧ z.ofLp 0 ^ 2 + z.ofLp 1 ^ 2 < a ^ 2 ∧ -K * z.ofLp 0 < z.ofLp 1 ∧ z.ofLp 1 < 0}; let G : Set E := {z : E | 0 < z.ofLp 0 ∧ z.ofLp 0 < a ∧ z.ofLp 1 = 0}; G ⊆ closure R) →
  (twoRay_base_subset_closure_left : ∀ (a c s : ℝ), 0 < s ∨ s = 0 ∧ c < 0 → let C : Set E := Metric.ball 0 a; let Gbase : Set E := {z : E | z ∈ C ∧ z.ofLp 1 = 0 ∧ 0 < z.ofLp 0}; let L : Set E := {z : E | z ∈ C ∧ 0 < z.ofLp 1 ∧ c * z.ofLp 1 - s * z.ofLp 0 < 0}; Gbase ⊆ closure L) →
  (twoRay_base_subset_closure_right : ∀ (a c s : ℝ), let C : Set E := Metric.ball 0 a; let Gbase : Set E := {z : E | z ∈ C ∧ z.ofLp 1 = 0 ∧ 0 < z.ofLp 0}; let R : Set E := {z : E | z ∈ C ∧ (z.ofLp 1 < 0 ∨ 0 < c * z.ofLp 1 - s * z.ofLp 0)}; Gbase ⊆ closure R) →
  (twoRay_origin_mem_closure_left : ∀ (a c s : ℝ), 0 < a → 0 < s ∨ s = 0 ∧ c < 0 → let C : Set E := Metric.ball 0 a; let L : Set E := {z : E | z ∈ C ∧ 0 < z.ofLp 1 ∧ c * z.ofLp 1 - s * z.ofLp 0 < 0}; 0 ∈ closure L) →
  (twoRay_origin_mem_closure_right : ∀ (a c s : ℝ), 0 < a → let C : Set E := Metric.ball 0 a; let R : Set E := {z : E | z ∈ C ∧ (z.ofLp 1 < 0 ∨ 0 < c * z.ofLp 1 - s * z.ofLp 0)}; 0 ∈ closure R) →
  (twoRay_other_subset_closure_left : ∀ (a c s : ℝ), 0 < s ∨ s = 0 ∧ c < 0 → let C : Set E := Metric.ball 0 a; let Gother : Set E := {z : E | z ∈ C ∧ ∃ (t : ℝ), 0 < t ∧ z.ofLp 0 = t * c ∧ z.ofLp 1 = t * s}; let L : Set E := {z : E | z ∈ C ∧ 0 < z.ofLp 1 ∧ c * z.ofLp 1 - s * z.ofLp 0 < 0}; Gother ⊆ closure L) →
  (twoRay_other_subset_closure_right : ∀ (a c s : ℝ), 0 < s ∨ s = 0 ∧ c < 0 → let C : Set E := Metric.ball 0 a; let Gother : Set E := {z : E | z ∈ C ∧ ∃ (t : ℝ), 0 < t ∧ z.ofLp 0 = t * c ∧ z.ofLp 1 = t * s}; let R : Set E := {z : E | z ∈ C ∧ (z.ofLp 1 < 0 ∨ 0 < c * z.ofLp 1 - s * z.ofLp 0)}; Gother ⊆ closure R) →
  (image_disjoint_of_injective : ∀ {f : E → E}, Function.Injective f → ∀ {A B : Set E}, Disjoint A B → Disjoint (f '' A) (f '' B)) →
  (chart_axis_eq_lineMap : ∀ (p0 p1 z : EuclideanSpace ℝ (Fin 2)), z.ofLp 1 = 0 → p0 + z.ofLp 0 • (p1 - p0) + z.ofLp 1 • PlanarRot90 (p1 - p0) = (AffineMap.lineMap p0 p1) (z.ofLp 0)) →
  (chart_axis_param_eq_lineMap : ∀ (p0 p1 : EuclideanSpace ℝ (Fin 2)) (t : ℝ), p0 + t • (p1 - p0) = (AffineMap.lineMap p0 p1) t) →
  (leftHalf_inter_subset_of_nonincident : ∀ (i : Fin γ.vertices.length) (C L : Set E), C ⊆ vertexLocalPieces.vertexDisk i → ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), ↑i ≠ j → ↑i ≠ j + 1 → sep.leftHalf j hj ∩ C ⊆ L) →
  (rightHalf_inter_subset_of_nonincident : ∀ (i : Fin γ.vertices.length) (C R : Set E), C ⊆ vertexLocalPieces.vertexDisk i → ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), ↑i ≠ j → ↑i ≠ j + 1 → sep.rightHalf j hj ∩ C ⊆ R) →
  let Good : Fin γ.vertices.length → Set E → Set E → Set E → Prop := fun (i : Fin γ.vertices.length) (C L R : Set E) => IsOpen C ∧ IsOpen L ∧ IsOpen R ∧ C ⊆ vertexLocalPieces.vertexDisk i ∧ (0 < ↑i → ↑i + 1 < γ.vertices.length → C = vertexLocalPieces.vertexDisk i) ∧ (↑i = 0 ∨ ↑i + 1 = γ.vertices.length → γ.vertices[↑i] ∉ C) ∧ L ⊆ C ∧ R ⊆ C ∧ IsConnected L ∧ IsConnected R ∧ Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧ Disjoint L R ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), sep.leftHalf j hj ∩ C ⊆ L) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), sep.rightHalf j hj ∩ C ⊆ R) ∧ C \ γ.relativeInterior = L ∪ R ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j, Nat.lt_of_succ_lt hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo 0 (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) ⊆ C) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j + 1, hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (1 - controlRadii.radius ⟨j + 1, hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) 1 ⊆ C) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j, Nat.lt_of_succ_lt hj⟩ → vertexLocalPieces.outgoingLeftAttachment j hj ⊆ L) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j, Nat.lt_of_succ_lt hj⟩ → vertexLocalPieces.outgoingRightAttachment j hj ⊆ R) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j + 1, hj⟩ → vertexLocalPieces.incomingLeftAttachment j hj ⊆ L) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j + 1, hj⟩ → vertexLocalPieces.incomingRightAttachment j hj ⊆ R) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j, Nat.lt_of_succ_lt hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo 0 (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure L) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j, Nat.lt_of_succ_lt hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo 0 (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure R) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j + 1, hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (1 - controlRadii.radius ⟨j + 1, hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) 1 ⊆ closure L) ∧ (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), i = ⟨j + 1, hj⟩ → ⇑(AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (1 - controlRadii.radius ⟨j + 1, hj⟩ / dist γ.vertices[j] γ.vertices[j + 1]) 1 ⊆ closure R) ∧ (0 < ↑i → ↑i + 1 < γ.vertices.length → γ.vertices[↑i] ∈ closure L) ∧ (0 < ↑i → ↑i + 1 < γ.vertices.length → γ.vertices[↑i] ∈ closure R);
  (hlen_two : 2 ≤ γ.vertices.length) →
  (hlen_pos : 0 < γ.vertices.length) →
  (hj0 : 0 + 1 < γ.vertices.length) →
  (hGoodInitial : ∃ (C : Set E) (L : Set E) (R : Set E), Good ⟨0, hlen_pos⟩ C L R) →
  let lastJ : ℕ := γ.vertices.length - 2;
  (hlastJ : lastJ + 1 < γ.vertices.length) →
  (hlastJ_succ : lastJ + 2 = γ.vertices.length) →
  ∃ (C : Set E) (L : Set E) (R : Set E), Good ⟨lastJ + 1, hlastJ⟩ C L R := by sorry
