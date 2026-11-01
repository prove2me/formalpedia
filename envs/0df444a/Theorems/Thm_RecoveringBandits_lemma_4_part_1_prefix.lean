-- Prove2me | Theorems.Thm_RecoveringBandits_lemma_4_part_1_prefix
-- name    : RecoveringBandits.lemma_4_part_1_prefix
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:07.898996+00:00
-- url     : https://prove2.me/theorems/d18ca124-4cdd-446b-875f-6b688548baad
-- title:
--   Proof of Lemma 4, Part 1: a prefix of periods in $D_j$ with sum $\le1<$ next prefix sums to exactly $1$
-- statement:
--   Let $j\ge1$ and let $d_1\le d_2\le\dots\le d_n$ be elements of $D_j=\{(2j-1)\cdot2^\ell\}_{\ell\ge0}$. If $1\le m<n$ and
--
--   $$\sum_{k=1}^{m}\frac1{d_k}\le1<\sum_{k=1}^{m+1}\frac1{d_k},$$
--
--   then $\displaystyle\sum_{k=1}^{m}\frac1{d_k}=1$.
--
--   This is why the greedy grouping of the arms of $I_j$ in increasing order of period produces groups of frequency exactly $1$ except possibly the last, hence at most $\lceil K_j\rceil$ groups.
--
--   Differences from the source:
--   - encoding: the periods d_{i_1} ≤ ⋯ ≤ d_{i_|I_j|} of the arms of I_j, indexed from 1 → any non-decreasing d : Fin n → ℕ with values in D_j, indexed from 0; reason: every such sequence is the sorted period list of some I_j; the first m terms are those with index < m
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, proof of Lemma 4, Part 1, p.ec5 (PDF p.37)

import Mathlib
import Definitions.Def_RecoveringBandits_roundUp

namespace RecoveringBandits

/-- **Proof of Lemma 4, Part 1**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, proof of Lemma 4,
Part 1, p.ec5 (PDF p.37): let `d_{i_1} ≤ d_{i_2} ≤ ⋯ ≤ d_{i_n}` be elements of
`D_j = {(2j − 1)·2^ℓ}_{ℓ ≥ 0}`. If `1 ≤ m < n` and
`∑_{k=1}^m 1/d_{i_k} ≤ 1 < ∑_{k=1}^{m+1} 1/d_{i_k}`, then `∑_{k=1}^m 1/d_{i_k} = 1`.

**Formalization Note.** The sorted list is `d : Fin n → ℕ` (monotone), indexed from `0`, so the
first `m` terms are those with index `< m`. `j ≥ 1` as in Lemma 4. -/
theorem lemma_4_part_1_prefix (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (d : Fin n → ℕ) (hmono : Monotone d)
    (hD : ∀ k, d k ∈ Dj j) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m < n)
    (hle : ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < m), 1 / (d k : ℝ) ≤ 1)
    (hgt : 1 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < m + 1), 1 / (d k : ℝ)) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < m), 1 / (d k : ℝ) = 1 := by sorry

end RecoveringBandits
