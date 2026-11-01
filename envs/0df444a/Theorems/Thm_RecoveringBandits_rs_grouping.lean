-- Prove2me | Theorems.Thm_RecoveringBandits_rs_grouping
-- name    : RecoveringBandits.rs_grouping
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:56:06.129856+00:00
-- url     : https://prove2.me/theorems/71f86db5-e144-403d-83ec-a3f4b76d32b4
-- title:
--   §4.2, Step 2 and display (5): the groups of R-S and $K[a]<\sum_i x_i+a$
-- statement:
--   Let $a\ge1$, $x\in[0,1]^N$, $d_i$ the rounding (4) of $x_i$, $I_j=\{i:d_i\in D_j\}$ and $K_j=\sum_{i\in I_j}1/d_i$. Then:
--
--   1. there are, for every $j\in[a]$, pairwise disjoint groups with union $I_j$, at most $\lceil K_j\rceil$ of them and each with $\sum_{i\in G}1/d_i\le1$, and offsets $o_i\in(-d_i,0]$ such that each group is a 1-PPP pulling arm $i$ every $d_i$ periods;
--   2. for every such grouping and offsets and every period $t\ge1$, the number of arms of $\bigcup_{j\in[a]}I_j$ pulled at $t$ is at most the total number of groups;
--   3. display (5):
--   $$K[a]=\sum_{j\in[a]}\Big\lceil\sum_{i\in I_j}1/d_i\Big\rceil<\sum_i x_i+a .$$
--
--   These are the two observations about Step 2 of the rounding–scheduling procedure: each arm lies in one group and is pulled with frequency $1/d_i$, and at most $K[a]$ arms are pulled at once.
--
--   Differences from the source:
--   - generalization: the groups built by the procedure (Lemma 4's greedy grouping and its 1-PPP construction) → clause 2 holds for every grouping and offsets with Lemma 4's properties; reason: the procedure's grouping is one of them
--   - reading: groups and 1-PPPs constructed by Lemma 4 (which also states running times) → existence of groups and offsets with the properties of Lemma 4's two bullets; reason: the observations quoted concern the groups, not the time to compute them
--   - encoding: the paper's ⌈·⌉ of a nonnegative real → Nat.ceil; reason: same values on nonnegative reals
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.2, Step 2 and display (5), p.13; Lemma 4, pp.12–13; proof of Lemma 4, pp.ec5–ec6

import Mathlib
import Definitions.Def_RecoveringBandits_IsRSRun

open Classical

namespace RecoveringBandits

/-- **§4.2, the grouping of R-S and display (5)**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2,
§4.2, Step 2, p.13 (PDF p.13), with Lemma 4 (pp.12–13) and its proof (pp.ec5–ec6). For `a ≥ 1`
and `x ∈ [0, 1]^N` with `d_i` the rounding (4):
1. for every `j ∈ [a]`, `I_j` splits into pairwise disjoint groups, at most `⌈K_j⌉` of them, each
   with frequency sum `≤ 1`, and there are offsets making every group a 1-PPP that pulls arm `i`
   every `d_i` periods ("each arm `i` is included in exactly one group and is pulled with
   frequency `1/d_i`");
2. for every such grouping, the number of arms pulled at the same time is at most the total
   number of groups;
3. display (5): `K[a] = ∑_{j ∈ [a]} ⌈∑_{i ∈ I_j} 1/d_i⌉ < ∑_i x_i + a`.

**Formalization Note.** No running time is stated (Lemma 4's `O(|I_j|)` clauses are not part of
this item). -/
theorem rs_grouping {N : ℕ} (a : ℕ) (ha : 1 ≤ a) (x : Fin N → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∃ (𝒢 : ℕ → Finset (Finset (Fin N))) (o : Fin N → ℤ), IsRSGrouping a x 𝒢 o) ∧
    (∀ (𝒢 : ℕ → Finset (Finset (Fin N))) (o : Fin N → ℤ), IsRSGrouping a x 𝒢 o →
      ∀ t : ℕ, 1 ≤ t →
        (((Finset.Icc 1 a).biUnion (Ij a x)).filter
          (fun i => (t : ℤ) ≡ o i [ZMOD (dnat a x i : ℤ)])).card ≤
          ∑ j ∈ Finset.Icc 1 a, (𝒢 j).card) ∧
    (∑ j ∈ Finset.Icc 1 a, (⌈Kj a x j⌉₊ : ℝ)) < ∑ i, x i + a := by sorry

end RecoveringBandits
