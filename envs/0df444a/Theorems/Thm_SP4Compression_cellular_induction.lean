-- Prove2me | Theorems.Thm_SP4Compression_cellular_induction
-- name    : SP4Compression.cellular_induction
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T11:01:31.661828+00:00
-- url     : https://prove2.me/theorems/dcab339c-e322-478a-b38a-1bb0870a204a
-- title:
--   Cellular induction step of the compression lemma
-- statement:
--   This is the cellular-induction (skeleton-extension) step of the compression lemma.
--
--   Let $X$ be a CW complex and let $(Y,\{y\})$ be a space pair that is cell-compressible at $y$ in the sense of `CellCompressible`.  Then every continuous map $f:X\to Y$ is homotopic to the constant map at $y$,
--   $$f\simeq \mathrm{const}_y .$$
--
--   The proof is the induction on the dimension of $X$ from the reference.  Assume $f$ has already been compressed on the $(k-1)$-skeleton.  For each $k$-cell $e^k$ of $X$, the composite of $f$ with the characteristic disk of $e^k$ is a generalized $k$-loop in $Y$; cell-compressibility homotopes it relative to the boundary to the constant loop at $y$.  The homotopy extension property for the CW pair $(X^k,X^{k-1})$ then extends these rel-boundary homotopies over the whole $k$-skeleton, and passing over all skeleta gives the global homotopy.
--
--   The genuinely topological input — extending a rel-boundary homotopy over attached cells and assembling the skeleta — is the content of this lemma.  Mathlib currently has neither a homotopy extension property for topological CW pairs nor this cellular induction, so it is left open rather than assumed.
-- source:
--   同伦论(2) Whitehead定理与胞腔逼近, 知乎专栏 https://zhuanlan.zhihu.com/p/22412267564 (压缩引理的胞腔归纳证明); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.7 (compression lemma).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Compression

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap

open scoped ContinuousMap
open ContinuousMap

universe u v

namespace SP4Compression

/-- The cellular-induction (skeleton-extension) step of the compression lemma.

Let `(X, A)` be a CW pair with `A = ∅` and let `(Y, {y})` be a pair of spaces whose relative
homotopy groups vanish, recorded as `CellCompressible Y y`.  Then every map from the CW
complex `X` to `Y` is homotopic to the constant map at `y`.

This is the induction on the dimension of `X` from the reference: assume `f` has been
compressed on the `(k-1)`-skeleton; for each `k`-cell `e^k`, the restriction of `f` to the
characteristic disk is a generalized `k`-loop, which `CellCompressible` makes homotopic to
the constant rel boundary; the homotopy extension property for CW pairs then extends this
over `X^k`.  The genuinely topological input — the extension of a rel-boundary homotopy
over attached cells and the passage to all skeleta — is the content of this lemma. -/
theorem cellular_induction
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] (y : Y)
    (hcell : CellCompressible Y y)
    (f : C(X, Y)) :
    Homotopic f (ContinuousMap.const X y) := by
  sorry

end SP4Compression
