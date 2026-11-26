-- Prove2me | Theorems.Thm_SP4TauCeti_exists_homotopicRel_forall_mapsTo_skeletonLT
-- name    : SP4TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T12:50:18.463561+00:00
-- url     : https://prove2.me/theorems/cbc1bb38-74e5-4253-9db1-3211c6f5631a
-- title:
--   Homotoping a map skeleton by skeleton (TauCeti)
-- statement:
--   This is TauCeti's `exists_homotopicRel_forall_mapsTo_skeletonLT`: **homotoping a map skeleton by skeleton**.
--
--   Let $S_n \subseteq Y$ be a sequence of subsets such that any map sending the $({<}n)$-skeleton into $S_n$ is homotopic, relative to that skeleton, to one sending the $(n+1)$-skeleton into $S_{n+1}$. Then any $f$ sending the base $D$ into $S_0$ is homotopic relative to $D$ to a map sending every skeleton into $S_n$.
--
--   TauCeti runs the $n$-th improving homotopy during the time interval $[1-2^{-n},\,1-2^{-n-1}]$ and concatenates them; continuity of the infinite concatenation follows from a quotient-map argument (a map out of $I\times\mathcal{C}$ is continuous as soon as it is continuous on $I$ times every skeleton). Only the statement is transplanted.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.6 (compression lemma) and the compression criterion; TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT, TauCeti.exists_homotopicRel_range_subset (https://github.com/TauCetiProject/TauCeti).

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Metric Set Topology Topology.RelCWComplex

universe u v

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y]

/-- **Homotoping a map skeleton by skeleton** (TauCeti,
`exists_homotopicRel_forall_mapsTo_skeletonLT`).  Let `S n ⊆ Y` be a sequence of subsets and
suppose that any map sending `skeletonLT C n` into `S n` is homotopic, relative to that skeleton,
to one sending `skeletonLT C (n+1)` into `S (n+1)`.  Then any `f` sending the base `D` into
`S 0` is homotopic relative to `D` to a map sending every skeleton `skeletonLT C n` into `S n`.

TauCeti performs the `n`-th improving homotopy during the time interval `[1-2⁻ⁿ, 1-2⁻ⁿ⁻¹]`
and concatenates them; continuity of the infinite concatenation follows because the map
`I × C → Y` is continuous as soon as it is continuous on `I` times every skeleton
(`exists_continuousMap_prod_complex_of_skeletonLT`, a quotient-map argument).  Only the statement
is transplanted. -/
theorem exists_homotopicRel_forall_mapsTo_skeletonLT (S : ℕ → Set Y)
    (step : ∀ (n : ℕ) (g : C(C, Y)),
      MapsTo g {x : C | (x : X) ∈ skeletonLT C n} (S n) →
        ∃ g' : C(C, Y), g.HomotopicRel g' {x : C | (x : X) ∈ skeletonLT C n} ∧
          MapsTo g' {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)} (S (n + 1)))
    (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} (S 0)) :
    ∃ g : C(C, Y), (∀ n : ℕ, MapsTo g {x : C | (x : X) ∈ skeletonLT C n} (S n)) ∧
      f.HomotopicRel g {x : C | (x : X) ∈ D} := by
  sorry

end SP4TauCeti
