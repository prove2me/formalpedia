-- Prove2me | Theorems.Thm_SP4WhiteheadSketch_compression_lemma
-- name    : SP4WhiteheadSketch.compression_lemma
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T10:41:26.03098+00:00
-- url     : https://prove2.me/theorems/0ecb778a-fc10-5b17-9abd-828588d92240
-- title:
--   Compression lemma: a cellular map into a weakly contractible CW complex is nullhomotopic
-- statement:
--   This is the compression lemma (压缩引理), specialized to the space pair $(Y,\{y\})$.
--
--   Let $(X,A)$ be a CW pair and $(Y,B)$ a pair of spaces with $B\neq\varnothing$.  If for every cell dimension $n$ of $X-A$ the relative homotopy group $\pi_n(Y,B,y_0)$ vanishes for all $y_0\in B$, then any map of pairs $f:(X,A)\to(Y,B)$ is homotopic relative to $A$ to a map $X\to B$.
--
--   The formal statement is the case $A=\varnothing$, $B=\{y\}$ (a single base point), with $f$ cellular: if $Y$ is a weakly contractible CW complex and $y\in Y$, then a cellular map $f:X\to Y$ is homotopic to the constant map at $y$,
--   $$f\simeq \mathrm{const}_y .$$
--   Because $\pi_n(Y,y)=0$ for every $n$, the long exact sequence of the pair $(Y,\{y\})$ gives $\pi_n(Y,\{y\})=0$ in every relevant degree, so the hypothesis of the general compression lemma is met.  Cellularity is the condition under which the inductive compression over the skeleta of $X$ is legitimate.
-- source:
--   同伦论(2) Whitehead定理与胞腔逼近, 知乎专栏 https://zhuanlan.zhihu.com/p/22412267564 (压缩引理、胞腔逼近定理、Whitehead 定理证明); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Proposition 4.8 (cellular approximation) and Theorem 4.5 (Whitehead).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4WhiteheadSketch
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap

open scoped ContinuousMap
open ContinuousMap

universe u v

namespace SP4WhiteheadSketch

/-- The compression lemma (压缩引理) in the form needed for the contractible case of
Whitehead's theorem.

Let `X` be a CW complex and let `Y` be a weakly contractible CW complex, with `y : Y` any
base point.  If `f : X → Y` is a cellular map, then `f` is homotopic to the constant map at
`y`, relatively to any subcomplex on which `f` already lands in `y`.

This is exactly the compression lemma of the reference applied to the CW pair `(X, A)` with
`A = ∅` and the space pair `(Y, {y})`: for every cell dimension `n` of `X`, the relative
homotopy group `π_n(Y, {y})` vanishes because all absolute groups `π_n(Y, y)` vanish, so the
identity map of pairs compresses into `{y}`.  The cellularity hypothesis is what makes the
cell-by-cell induction (over the skeleta of `X`) legitimize the compression. -/
theorem compression_lemma
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (y : Y) (hweak : SP4WeakHomotopy.WeaklyContractible Y)
    (f : C(X, Y)) (hfcell : CellularMap f) :
    Homotopic f (ContinuousMap.const X y) := by
  sorry

end SP4WhiteheadSketch
