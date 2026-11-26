-- Prove2me | Theorems.Thm_SP4Compression_exists_homotopicRel_range_subset
-- name    : SP4Compression.exists_homotopicRel_range_subset
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T12:17:08.847932+00:00
-- url     : https://prove2.me/theorems/29b0cba8-f8a5-5824-af13-e8bdd591c301
-- title:
--   Compression lemma (TauCeti / Hatcher), relative CW form
-- statement:
--   This is the statement of the compression lemma (Hatcher, Lemma 4.6) transplanted from TauCetiProject/TauCeti into the Mathlib-only vocabulary of prove2me.
--
--   Let $(C,D)$ be a relative CW complex with base $D$, let $y\in Y$, and assume the cubical compression criterion `CellCompressible Y y` — equivalently $\pi_n(Y,\{y\})=0$ for all $n$, which in TauCeti is phrased as: every map of pairs $(D^n,S^{n-1})\to(Y,\{y\})$ is homotopic relative to $S^{n-1}$ into $\{y\}$. Then every continuous map $f:C\to Y$ sending $D$ into $y$ is homotopic relative to $D$ to a map whose range lies in $\{y\}$, i.e. to the constant map at $y$:
--   $$f\simeq_D \mathrm{const}_y,\qquad \mathrm{range}(g)\subseteq\{y\}.$$
--
--   TauCeti proves this by induction over the skeleta of the relative CW complex, compressing the characteristic disk of each $n$-cell by the hypothesis and extending the rel-boundary homotopy with the homotopy extension property for CW pairs. That proof depends on TauCeti's `RelHomotopyGroup`, `MappingCylinder` and CW cell-extension infrastructure, none of which exists in the prove2me Mathlib environment; only the statement is transplanted, and the proof is left open here.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.6 (compression lemma); TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_range_subset (https://github.com/TauCetiProject/TauCeti); 同伦论(2) Whitehead定理与胞腔逼近, https://zhuanlan.zhihu.com/p/22412267564.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Compression

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap Set Topology Topology.RelCWComplex

open scoped ContinuousMap
open ContinuousMap Set Topology Topology.RelCWComplex

universe u v

namespace SP4Compression

/-- Transplant of the TauCeti / Hatcher compression lemma (Lemma 4.6), relative CW form,
stated in the Mathlib-only vocabulary available on prove2me.

Let `(C, D)` be a relative CW complex with base `D`, let `y : Y`, and assume the cubical
compression criterion `CellCompressible Y y` (equivalently `πₙ(Y, {y}) = 0` for all `n`;
in TauCeti this is the hypothesis on maps `(closedBall 0 1, sphere 0 1) → (Y, {y})`).
Then every `f : C → Y` sending `D` to `y` is homotopic relative to `D` to a map whose range
lies in `{y}`, i.e. to the constant map at `y`.

In TauCeti this is `TauCeti.exists_homotopicRel_range_subset`, proved by induction on the
skeleta using the CW homotopy extension property.  That proof depends on TauCeti's
`RelHomotopyGroup`, `MappingCylinder` and CW cell-extension infrastructure, none of which is
available in the prove2me Mathlib environment; only the statement is transplanted here. -/
theorem exists_homotopicRel_range_subset
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (C D : Set X) [RelCWComplex C D]
    (Y : Type v) [TopologicalSpace Y] (y : Y)
    (hcell : CellCompressible Y y)
    (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} {y}) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ D} ∧ range g ⊆ {y} := by
  sorry

end SP4Compression
