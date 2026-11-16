-- Prove2me | Theorems.Thm_TetraOT_Supplement_theorem_10_2
-- name    : TetraOT.Supplement.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:44:28.88841+00:00
-- url     : https://prove2.me/theorems/f9864bc5-9381-4b06-bacc-170805b8a98b
-- title:
--   Theorem 10.2 — the $3/8,3/8$-Multi Tetrahedral Protocol (corrected: $n = 8k$ and $\mathbb E[g]/m \to 81/256$)
-- statement:
--   Let $n = 8k$ with $k\ge1$, $m = n/4 = 2k$, let $\rho$ be uniform on $S_n$, and deal $(3n/8, 3n/8; n/4)$: Alice gets the cards at positions $0,\dots,3k-1$, Bob those at positions $3k,\dots,6k-1$, and $2k$ cards are discarded. Run the Multi Tetrahedral Protocol (Fig. 31) on these hands. Then:
--
--   1. (correctness and security) for every $k\ge1$ the protocol perfectly realizes the ideal functionality ½ROT$_g$ against semi-honest parties, exactly as in Theorem 10.1;
--   2. (yield) the expected number of oblivious transfers per rank converges:
--   $$\frac{\mathbb E[g(\rho)]}{m}\ \longrightarrow\ \frac{81}{256}\qquad(k\to\infty),$$
--   equivalently $\mathbb E[g(\rho)]/n \to 81/1024$.
--
--   Equal hands of $3n/8$ cards improve the per-rank rate from $9/32$ for the $(2m,m;m)$ deal of Theorem 10.1 to $81/256$, the maximum of the App. B rate over hand proportions (Lemma B.1).
--
--   Differences from the source:
--   - reading: "securely against semi-honest adversaries" / "perfectly secure against semi-honest adversaries" / "information-theoretically secure for honest-but-curious parties" (§2: "perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations") → the published TetraOT.PerfectSemiHonestRealizes: equal output laws, and for each party a simulator seeing only that party's ideal output that reproduces the joint law of (view, both outputs); reason: the notion §2 names and the one the live mission's Theorem 4.1 uses; perfect and standalone
--   - reading: the parties' views → each party's view is its whole ordered hand and the whole public transcript (S_A(ρ,2), S_A(ρ,1), S_B(ρ,1), S_B(ρ,2) and every M_r); reason: this is everything a party sees in Fig. 31
--   - reading: correct; Out: g(ρ), {P_A(ρ, r)} (Fig. 31); ½ROT_g → outputs are the role map (who sends at each rank, none off G(ρ); it determines g(ρ)) and the per-rank results; the ideal law idealMulti draws the role map from its real law and independent uniform ROT bits per rank, oriented by role; reason: G(ρ) is common knowledge (p.12) and the paper's privacy claim is that the distribution for any successful r is uniform regardless of the other ranks (§10.3)
--   - reading: run the single instance Tetrahedral Protocol on each r ∈ G(ρ), including the (1,2;1) ranks → the two-card party is the sender and applies A to the suits of its two rank-r cards in position order; the one-card party applies B to M_r and its suit; reason: the per-rank instance of p.11–12, with the reversed (1,2;1) case as on p.11
--   - reading: the four cards of rank r are 'mapped in the natural isomorphic way from {0,1,2,3}' (suits assigned arbitrarily) → suit of card x is x / m; reason: one fixed choice of the arbitrary suit assignment; the claims hold for every fixed choice
--   - encoding: Bob's result (y₀, y₁) ∈ {0•, 1•, •0, •1} → the pair (s, m_s) of Booleans, true = 1; reason: one-to-one recoding (right dot = s = 0, Fig. 5 caption), as in the published bobTable
--   - correction: n = 4m > 4 (any multiple of 4), hands of 3n/8 cards → n = 8k with k ≥ 1, m = 2k, hands of 3k cards each; reason: hands of 3n/8 cards exist only when 8 ∣ n: for n = 12 (m = 3) the hand size 4.5 is not an integer, so the 3/8, 3/8 protocol is undefined there; the statement is kept for every n where it is defined
--   - correction: E[g(ρ)] → 81/256 n → E[g(ρ)] / m → 81/256 (m = n/4 = 2k), i.e. E[g(ρ)] / n → 81/1024; reason: the printed limit is false: App. B (p.17) gives E[g] = 192m³ab(1−(a+b))(4m(a+b)−2)/((4m−1)(4m−2)(4m−3)), which at a = b = 3/8 is 27m³(3m−2)/(4(4m−1)(4m−2)(4m−3)), so E[g]/n → 81/1024 ≠ 81/256 (at n = 8 an exhaustive count gives E[g] = 36/35); the limit 81/256 holds per rank, the form App. B ends with ('≈ 81/256 m')
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 10.2, p.13, with §10.4, p.13, and App. B, pp.16–17 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes
import Definitions.Def_TetraOT_Supplement_multiRun
import Definitions.Def_TetraOT_Supplement_idealMulti
import Definitions.Def_TetraOT_Supplement_expectedYield

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT Filter Topology

/-- **Theorem 10.2 (the 3/8, 3/8-Multi Tetrahedral Protocol), corrected** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 10.2, p.13, with
§10.4, p.13, and App. B, pp.16–17; p. = PDF page, the PDF has no printed page numbers): "Let n = 4m > 4
and let ρ ←$ S_n be distributed uniformly. The 3/8, 3/8-Multi Tetrahedral Protocol is correct,
information-theoretically secure for honest-but-curious parties, and it provides E[g(ρ)] → 81/256 n
instances of ½ROT."

Let `n = 8k`, `k ≥ 1`, `m = n/4 = 2k`. With `ρ` uniform on `S_n`, Alice holding the cards at
positions `0, …, 3k − 1`, Bob those at positions `3k, …, 6k − 1` and the remaining `2k` discarded (a
`(3n/8, 3n/8; n/4)` deal), and the Multi Tetrahedral Protocol of Fig. 31 run on these hands:
1. for every `k ≥ 1` the protocol perfectly realizes ½ROT_g (`idealMulti`) against a semi-honest Alice
   and a semi-honest Bob (correctness and security, as in Theorem 10.1);
2. the expected yield per rank tends to `81/256`:
$$\frac{\mathbb E[g(\rho)]}{m} \longrightarrow \frac{81}{256} \quad (k \to \infty),$$
   equivalently `𝔼[g(ρ)]/n → 81/1024`.

**Formalization Note.** Two corrections of the printed statement. (i) Hands of `3n/8` cards exist only
when `8 ∣ n`, so the theorem is stated for `n = 8k`. (ii) The printed limit "E[g(ρ)] → 81/256 n" is
false: App. B (p.17) gives `𝔼[g] = 192m³ab(1−(a+b))(4m(a+b)−2)/((4m−1)(4m−2)(4m−3))`, which at
`a = b = 3/8` is `27m³(3m−2)/(4(4m−1)(4m−2)(4m−3))`, so `𝔼[g]/n → 81/1024`; the limit `81/256` holds
per rank `m`, the form App. B itself ends with ("𝔼[∑Z_r] ≈ 81/256 m"). -/
theorem theorem_10_2 :
    (∀ k : ℕ, 1 ≤ k →
      PerfectSemiHonestRealizes (multiDeal (2 * k))
        (multiViewA (2 * k) (3 * k) (3 * k) (by omega)) (multiViewB (2 * k) (3 * k) (3 * k) (by omega))
        (multiAliceOut (2 * k) (3 * k) (3 * k) (by omega)) (multiBobOut (2 * k) (3 * k) (3 * k) (by omega))
        (idealMulti (2 * k) (3 * k) (3 * k) (by omega))) ∧
    Tendsto (fun k : ℕ => expectedYield (2 * k) (3 * k) (3 * k) (by omega) / (2 * k : ℝ)) atTop
      (𝓝 (81 / 256)) := by sorry

end TetraOT.Supplement
