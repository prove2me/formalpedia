-- Prove2me | Theorems.Thm_RobersonCx_lemma_17
-- name    : RobersonCx.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:09.787199+00:00
-- url     : https://prove2.me/theorems/753081f9-d670-4d8f-8869-b4a016bbb6f1
-- title:
--   Lemma 17 — pathwidth bounds for $B^{(r)}_n$ and its vertex and edge deletions
-- statement:
--   Let $r\ge2$ and $n>2r$. Then:
--
--   1. $\mathrm{pw}(B^{(r)}_n)\le 2r$;
--   2. deleting $r$ consecutive $u$-vertices $\{u_a,\dots,u_{a+r-1}\}$, or $r$ consecutive $v$-vertices $\{v_a,\dots,v_{a+r-1}\}$, leaves pathwidth at most $r$;
--   3. deleting any spoke $v_iu_i$ or long edge $v_iu_{i+r}$ leaves pathwidth at most $2r-1$.
--
--   These are the host-side bounds for the cubic graphs in Lemma 19.
--
--   Differences from the source:
--   - encoding: $\mathrm{pw}(\cdot)\le k$ → `PwLE · k`: a `GaussianSweep.IsPathDecomposition` with bags of size at most $k+1$; reason: a path decomposition indexed along the path; same notion
--   - encoding: vertices $u_i$, $v_i$ → `Sum.inl i`, `Sum.inr i` on `ZMod n ⊕ ZMod n`; reason: a labelling of the vertex set; same graph
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 17, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 17 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.5, p.15 (PDF p.17)). Let `r ≥ 2` and `n > 2r`. Then: (i) `pw(B^(r)_n) ≤ 2r`;
(ii) deleting `r` consecutive `u`-vertices, or `r` consecutive `v`-vertices, leaves pathwidth at most `r`;
(iii) deleting any spoke or long edge leaves pathwidth at most `2r − 1`.

**Formalization Note** `u_i = Sum.inl i`, `v_i = Sum.inr i`. Consecutive `u`-vertices: `{u_a, …, u_{a+r−1}}`;
spoke `v_iu_i`; long edge `v_iu_{i+r}`. Vertex deletion is the induced subgraph on the complement. -/
theorem lemma_17 (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    PwLE (splitB n r) (2 * r) ∧
    (∀ a : ZMod n,
      PwLE ((splitB n r).induce
        ({x | ∃ j < r, x = Sum.inl (a + (j : ZMod n))} : Set (ZMod n ⊕ ZMod n))ᶜ) r ∧
      PwLE ((splitB n r).induce
        ({x | ∃ j < r, x = Sum.inr (a + (j : ZMod n))} : Set (ZMod n ⊕ ZMod n))ᶜ) r) ∧
    (∀ i : ZMod n,
      PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl i)}) (2 * r - 1) ∧
      PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + (r : ZMod n)))}) (2 * r - 1)) := by sorry

end RobersonCx
