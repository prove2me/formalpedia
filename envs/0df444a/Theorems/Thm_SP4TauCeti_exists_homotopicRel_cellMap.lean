-- Prove2me | Theorems.Thm_SP4TauCeti_exists_homotopicRel_cellMap
-- name    : SP4TauCeti.exists_homotopicRel_cellMap
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T12:50:23.446339+00:00
-- url     : https://prove2.me/theorems/f39c72eb-cb70-5296-8db4-0cccde5d8bd5
-- title:
--   Homotoping a map one dimension at a time (TauCeti)
-- statement:
--   This is TauCeti's `exists_homotopicRel_cellMap`: **homotoping a map one dimension at a time**.
--
--   Let $f : \mathcal{C}\to Y$ and, for every $n$-cell $j$ with characteristic map $\Phi_j$, let $f\circ\Phi_j$ be homotopic relative to the boundary sphere to a map $\psi_j$ of the closed unit ball. Then $f$ is homotopic relative to the $({<}n)$-skeleton to a map $g$ with $g\circ\Phi_j = \psi_j$ for every $n$-cell $j$.
--
--   TauCeti's proof glues the cell homotopies over the closed $n$-cells and extends the result from the $(n+1)$-skeleton to all of $\mathcal{C}$ using the homotopy extension property of that skeleton. Those ingredients rely on TauCeti's CW cell-extension and NDR-pair machinery, absent from Mathlib, so only the statement is transplanted.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.6 (compression lemma) and the compression criterion; TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT, TauCeti.exists_homotopicRel_range_subset (https://github.com/TauCetiProject/TauCeti).

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4TauCeti

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Metric Set Topology Topology.RelCWComplex

universe u v

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y]

/-- **Homotoping a map one dimension at a time** (TauCeti, `exists_homotopicRel_cellMap`).
Let `f : C → Y` and, for every `n`-cell `j` with characteristic map `Φⱼ = cellMap j`, let
`f ∘ Φⱼ` be homotopic relative to the boundary sphere to a map `ψ j` of the closed unit ball.
Then `f` is homotopic relative to the `(<n)`-skeleton to a map `g` with `g ∘ Φⱼ = ψ j` for every
`n`-cell `j`.

TauCeti proves this by gluing the cell homotopies over the closed `n`-cells
(`exists_continuousMap_prod_skeletonLT_succ`) and extending the result from
`skeletonLT C (n+1)` to all of `C` using the homotopy extension property of that skeleton
(`hasHomotopyExtensionProperty_skeletonLT`).  These use TauCeti's CW cell-extension and NDR-pair
machinery, absent from Mathlib; only the statement is transplanted. -/
theorem exists_homotopicRel_cellMap (n : ℕ) (f : C(C, Y))
    (ψ : cell C n → C(closedBall (0 : Fin n → ℝ) 1, Y))
    (hψ : ∀ j, (f.comp (cellMap j)).HomotopicRel (ψ j) {z | (z : Fin n → ℝ) ∈ sphere 0 1}) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C n} ∧
      ∀ j z, g (cellMap j z) = ψ j z := by
  sorry

end SP4TauCeti
