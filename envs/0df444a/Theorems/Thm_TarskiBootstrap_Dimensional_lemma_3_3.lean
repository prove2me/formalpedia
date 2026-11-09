-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_lemma_3_3
-- name    : TarskiBootstrap.Dimensional.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:30:40.216202+00:00
-- url     : https://prove2.me/theorems/a50cafc6-48fa-4fb2-aa4a-9545b2ce4e43
-- title:
--   Lemma 3.3 — Chain injectivity, monotonicity and unique fixed point
-- statement:
--   Let $n,k,t$ be positive integers and let $F$ consist of monotone maps $[n]^k\to[n]^k$, each with a unique fixed point. Let $A$ be an antichain containing every possible fixed point. For the prescribed chain constructor associated with $A$,
--
--   $$C_t:F^t\longrightarrow([n]^{tk}\to[n]^{tk})\quad\text{is injective},$$
--   $$\forall\mathbf f\in F^t,\quad C_t(\mathbf f)\text{ is monotone},$$
--   $$\forall\mathbf f\in F^t,\ \forall\mathbf x,\quad C_t(\mathbf f)(\mathbf x)=\mathbf x\iff\mathbf x=(f_1^*,\ldots,f_t^*).$$
--
--   The last formula asserts existence and uniqueness at the specified point. The theorem provides the actual-map indexing required by the adversary construction.
--
--   Differences from the source:
--   - encoding: positive integers n, k and t and the grid [n]^(tk) → PNat parameters, Fin coordinates, and the block grid with the explicit flattenBlocks order equivalence; reason: the coordinate bijection preserves the full grid and its coordinatewise order
--   - encoding: the unique fixed point f* → a total choice selector used only under the unique-fixed-point assumptions; reason: on these instances the chosen answer is forced; the no-fixed-point fallback is never used
--   - encoding: a unique fixed point, namely the tuple of component fixed points → a pointwise iff between being fixed and equality to that tuple; reason: the iff states both existence and uniqueness, including the identified value
--   - reading: a family of hard instances for Tarski(n, k), a term the source does not define separately → a set of monotone endomaps of the grid, with no further condition; reason: hardness enters only through the adversary witness; this is the broadest reading, so every source instance is covered
--   - encoding: one-based blocks 1,...,t and the sentinel sigma = t+1 → zero-based Fin t blocks and the sentinel t in firstNonfixed; reason: a uniform shift by one; the guard in chain never reads the sentinel as a block
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.3, PDF/printed p. 12, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_ChainFamily

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Lemma 3.3, PDF/printed p. 12: all three conclusions. -/
theorem lemma_3_3 {n k : ℕ+} (t : ℕ+)
    (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A)
    (hcontains : possibleAnswers F ⊆ A) :
    Function.Injective (chainOnFamily t A F) ∧
    (∀ f, Monotone (chainOnFamily t A F f)) ∧
    (∀ f, ∀ x, chainOnFamily t A F f x = x ↔
      x = fun i => fixedPoint (f i).val) := by sorry

end TarskiBootstrap.Dimensional
