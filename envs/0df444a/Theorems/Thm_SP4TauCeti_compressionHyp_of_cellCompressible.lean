-- Prove2me | Theorems.Thm_SP4TauCeti_compressionHyp_of_cellCompressible
-- name    : SP4TauCeti.compressionHyp_of_cellCompressible
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T12:50:26.628056+00:00
-- url     : https://prove2.me/theorems/235f17b3-8a52-4c4a-a254-180503a91890
-- title:
--   Compression criterion: CellCompressible implies ball compression
-- statement:
--   This is Hatcher's **compression criterion**: the vanishing of the relative homotopy groups $\pi_n(Y,\{y\})$ is equivalent to the condition that every map of pairs $(D^n,S^{n-1})\to(Y,\{y\})$ be homotopic relative to $S^{n-1}$ into $\{y\}$.
--
--   Here the vanishing hypothesis is recorded in Mathlib's cubical model as `SP4Compression.CellCompressible Y y` (every based generalized $n$-loop $I^n\to Y$ with boundary at $y$ is rel-boundary nullhomotopic), while the conclusion uses the sup-norm closed ball/sphere $D^n = \overline{B}_1(0)$, $S^{n-1}$ of the CW characteristic maps. The two domain models are homeomorphic, $I \simeq_t [-1,1]$ coordinatewise, with the cube boundary corresponding to the sphere, and transporting a rel-boundary homotopy across this homeomorphism is the content of the criterion.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.6 (compression lemma) and the compression criterion; TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT, TauCeti.exists_homotopicRel_range_subset (https://github.com/TauCetiProject/TauCeti).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Compression

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Metric Set Topology Topology.RelCWComplex

universe v

namespace SP4TauCeti

variable (Y : Type v) [TopologicalSpace Y] (y : Y)

/-- The compression criterion (Hatcher, the paragraph after Lemma 4.6): the vanishing of the
relative homotopy groups `πₙ(Y, {y})` — recorded in Mathlib's cubical model as
`SP4Compression.CellCompressible Y y` — implies that every map of the closed unit ball
`Dⁿ = closedBall (0 : Fin n → ℝ) 1` into `Y` carrying the sphere `Sⁿ⁻¹` into `{y}` is homotopic,
relative to the sphere, to a map whose image lies in `{y}`.

This bridges Mathlib's cubical model (generalized loops `Iⁿ → Y`, `Cube.boundary`) used in
`CellCompressible` with the sup-norm ball/sphere model used by CW characteristic maps and by
TauCeti's compression lemma.  The two models are homeomorphic (`I ≃ₜ [-1,1]` coordinatewise)
with boundary corresponding to sphere; transplanting a rel-boundary homotopy across this
homeomorphism is the content of this criterion. -/
theorem compressionHyp_of_cellCompressible (hcell : SP4Compression.CellCompressible Y y) :
    ∀ n : ℕ, ∀ g : C(closedBall (0 : Fin n → ℝ) 1, Y),
      MapsTo g {z | (z : Fin n → ℝ) ∈ sphere 0 1} {y} →
        ∃ g' : C(closedBall (0 : Fin n → ℝ) 1, Y),
          g.HomotopicRel g' {z | (z : Fin n → ℝ) ∈ sphere 0 1} ∧ range g' ⊆ {y} := by
  sorry

end SP4TauCeti
