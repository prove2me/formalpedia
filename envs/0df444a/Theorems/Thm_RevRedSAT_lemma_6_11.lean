-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_11
-- name    : RevRedSAT.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:10.789121+00:00
-- url     : https://prove2.me/theorems/646ae036-fdf5-4f48-b574-c8fc42bc8656
-- title:
--   Lemma 6.11 — two random buckets in $[8k]$ place a fixed set with probability $>15/16$
-- statement:
--   Let $k\ge1$. Independently for each element $u$, choose a uniformly random unordered pair $g(u)$ of distinct buckets in $[8k]$. For every fixed set $S$ of at most $k$ elements, with probability greater than $15/16$:
--
--   1. the elements of $S$ can be placed in distinct allowed buckets;
--   2. the multigraph with the buckets as vertices and the pairs $g(u)$, $u\in S$, as labelled edges is a forest.
--
--   This is the placement principle behind cuckoo hashing.
--
--   Differences from the source:
--   - encoding: independent uniform random pairs, probability → a ratio of counts over the uniform space of maps [n] → (2-subsets of [8k]); reason: the product distribution is uniform on maps
--   - encoding: the multigraph is a forest → every nonempty set E of its edges touches more than |E| buckets; reason: equivalent for loopless multigraphs; parallel pairs count as cycles (p.46)
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.11, p.44 (printed) = PDF p.46

import Mathlib
import Definitions.Def_RevRedSAT_Placeable

set_option autoImplicit false

namespace RevRedSAT

open Classical in
/-- **Lemma 6.11 (two choices place a fixed set).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.11, p.44: "Let k ≥ 1. Independently for each element u, choose a uniformly random
unordered pair g(u) of distinct buckets in [8k]. For every fixed set S of at most k elements, with
probability greater than 15/16 the elements of S can be placed in distinct allowed buckets. In fact,
the multigraph with buckets as vertices and the pairs g(u), u ∈ S, as labeled edges is a forest with
that probability."

For every `n`, the sample space is the finite set of maps `g` from `[n]` to the 2-element subsets of
`[8k]`, uniform. For every `S` with `|S| ≤ k`, more than a `15/16` fraction of the maps place `S` in
distinct allowed buckets, and more than a `15/16` fraction make the bucket multigraph of `S` a
forest.

**Formalization Note** Probabilities are ratios of counts; the forest condition counts parallel pairs
as cycles (`IsForestOn`). -/
theorem lemma_6_11 (n k : ℕ) (hk : 1 ≤ k) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    (15 / 16 : ℝ) <
        ((Finset.univ.filter fun g : Fin n → {T : Finset (Fin (8 * k)) // T.card = 2} =>
          Placeable (fun u => (g u).1) S).card : ℝ) /
          Fintype.card (Fin n → {T : Finset (Fin (8 * k)) // T.card = 2}) ∧
    (15 / 16 : ℝ) <
        ((Finset.univ.filter fun g : Fin n → {T : Finset (Fin (8 * k)) // T.card = 2} =>
          IsForestOn (fun u => (g u).1) S).card : ℝ) /
          Fintype.card (Fin n → {T : Finset (Fin (8 * k)) // T.card = 2}) := by sorry

end RevRedSAT
