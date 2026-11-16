-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_Supplement_lemma_3_7
-- name    : PlanarDFVS.SingleExp.Supplement.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:33:30.873288+00:00
-- url     : https://prove2.me/theorems/b7bcae9e-3fba-4084-9ecf-16a21eca88d4
-- title:
--   Lemma 3.7 — DFVS in Σ_{h≤min(p,k)} C(p,h)·n^{O(1)} time, p positive vertices
-- statement:
--   Let $D$ be a loopless plane digraph (parallel arcs allowed) with $n$ vertices and a fixed embedding, given together with a budget $k\in\mathbb N$ in the exact input format (vertex count, budget, directed support bits, compressed rotation system). Let $p$ be the number of positive vertices of $D$, i.e. those with $w(v)=b(v)-1>0$, put $N=\max(1,n)$, let $|k|$ be the bit length of $k$ and let $\ell$ be the encoded input length.
--
--   There is one deterministic binary program $A$, together with constants $C,S>0$ and degrees $d,e\in\mathbb N$ fixed before every input, such that on every such input $A$ halts, returns either Fail or a directed feedback vertex set of $D$ of size at most $k$, returns a set exactly when one exists, and satisfies
--
--   $$\text{time}\le C\Bigl(\sum_{h=0}^{\min\{p,k\}}\binom{p}{h}\Bigr)(N+|k|)^{d},\qquad\text{space}\le S\,\ell^{e}.$$
--
--   This is the subroutine Exact of the $6.75^k$ algorithm (Theorem 4.1), called when $L\le 3k$ and hence $p\le 3k$.
--
--   Differences from the source:
--   - reading: deterministic algorithm, n^{O(1)} time and polynomial space with the machine model unspecified → one finite binary instruction program with charged bit operations, fixed C, S > 0 and d, e before every input; reason: same convention as the published Theorems 4.2 and 5.2; no cost certificate or oracle
--   - reading: a plane digraph as input → n, binary k, the directed support bits and the rotation system restricted to one representative per parallel class (the published protectedInput format with k in place of the protected set); reason: the embedding is part of the input as for Lemma 3.6; p is still the positive count of the full multigraph drawing
--   - reading: find a DFVS of size at most k (if it exists) → returns a DFVS of size at most k or Fail, and returns a set if and only if one exists; reason: the natural reading of "if it exists" for a decision-and-search algorithm, as in the published Theorem 5.2
--   - encoding: Σ_h C(p,h) · n^{O(1)} → C · (Σ_h C(p,h)) · (polynomial factor)^d; reason: the polynomial factor is uniform in h, so it factors out of the sum; max(1,n) avoids a vanishing bound at n = 0
--   - reading: n^{O(1)}, with the budget k part of the input → (max(1,n) + bit length of k)^d; reason: the base machine charges a load by the bit length of the value read and every correct program must read k (on the directed digon, p = 0 and the answer differs between k = 0 and k ≥ 1), so a factor in n alone is unattainable for huge k; for k < 2^{n^{O(1)}} (in particular k ≤ n, the only case Theorem 4.1 uses) the two coincide
--   - encoding: polynomial space → maximum live workspace along the run at most S·ℓ^e; reason: same convention as the published Theorems 4.2 and 5.2
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 8 (PDF p. 8), Lemma 3.7

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Supplement_Exact

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp.Supplement

open PlanarDFVS.SingleExp

theorem lemma_3_7 :
    ∃ (A : Program) (C S : ℝ) (d e : ℕ), 0 < C ∧ 0 < S ∧ ExactGuarantee A C d S e := by sorry

end PlanarDFVS.SingleExp.Supplement
