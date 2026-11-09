-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_8
-- name    : ThreshRankBIS.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:10:01.01767+00:00
-- url     : https://prove2.me/theorems/965e5cd3-48c7-42bc-8f40-277176aa2b0f
-- title:
--   Lemma 8 — low-deficit coverage, $0\le Z_G(\lambda)-Z_T\le Z_{\ge T}$
-- statement:
--   Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, let $T\ge1$ be an integer and $\lambda>0$. Let $I_1,\dots,I_M$ be a list of independent sets that contains every maximal independent set of size at least $n-T+1$ (a successful enumeration), and put $\mathcal J_T=\bigcup_j2^{I_j}$, $Z_T=\sum_{J\in\mathcal J_T}\lambda^{|J|}$. Then $\mathcal J_T$ contains every independent set $J$ with $t(J\cap X)<T$, and consequently
--
--   $$
--   0\le Z_G(\lambda)-Z_T\le Z_{\ge T}.
--   $$
--
--   The covered family therefore misses only independent sets whose left part has deficit at least $T$, and the container bound of Section 4 makes their weight small.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - generalization: on a successful enumeration (the returned list of maximal independent sets, with X and Y included) → a list L : Fin M → Finset V of independent sets (not necessarily maximal) containing every maximal independent set of size at least n − T + 1; reason: this is the property of a successful enumeration that the lemma uses; the returned list consists of maximal independent sets, so it is an instance; X and Y are maximal independent of size n, so they are among the required sets
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with the same lower bound; reason: the statement is about the combinatorial weights only and holds for every real λ in the range; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 8, p.11; definitions of 𝒥_T, Z_T, Z_{≥T}, §3.3, p.11

import Mathlib
import Definitions.Def_ThreshRankBIS_mWeight
import Definitions.Def_ThreshRankBIS_unionTrial
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Lemma 8 (Low-deficit coverage)**, p.11. Let `T ≥ 1` and let `I_1, …, I_M` be a list of
independent sets containing every maximal independent set of size at least `n − T + 1` (a
successful enumeration). Then `𝒥_T = ⋃_j 2^{I_j}` contains every independent set `J` with
`t(J ∩ X) < T`, and consequently `0 ≤ Z_G(λ) − Z_T ≤ Z_{≥T}` for every `λ > 0`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 8, p.11;
`𝒥_T`, `Z_T`, `Z_{≥T}` defined in §3.3, p.11.

**Formalization Note.** The list is `L : Fin M → Finset (V n)`; `Z_T` is `unionWeight L λ`, which
counts each set of the union once. "Successful enumeration" is the hypothesis `hcov` (the output
of step 3 of the algorithm, p.16, which also includes `X` and `Y`; those are maximal independent
of size `n`, so `hcov` already requires them). `λ` is real. -/
theorem lemma_8 {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (T : ℕ) (hT : 1 ≤ T) {M : ℕ} (L : Fin M → Finset (V n)) (hind : ∀ j, IsIndep E (L j))
    (hcov : ∀ I : Finset (V n), IsMaxIndep E I → (n : ℤ) - T + 1 ≤ #I → ∃ j, L j = I)
    (lam : ℝ) (hlam : 0 < lam) :
    (∀ J : Finset (V n), IsIndep E J → deficit E (leftPart J) < T → J ∈ unionFamily L) ∧
      0 ≤ hardcoreZ E lam - unionWeight L lam ∧
      hardcoreZ E lam - unionWeight L lam ≤ Ztail E T lam := by sorry

end ThreshRankBIS
