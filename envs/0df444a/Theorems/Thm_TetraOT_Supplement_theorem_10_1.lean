-- Prove2me | Theorems.Thm_TetraOT_Supplement_theorem_10_1
-- name    : TetraOT.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:43:55.812852+00:00
-- url     : https://prove2.me/theorems/5b609380-b28f-46c8-9a4a-7262c8b50aef
-- title:
--   Theorem 10.1 — the Multi Tetrahedral Protocol on $S_n$ is perfectly secure and yields $\mathbb E[g(\rho)] = \Theta(n)$ ROTs
-- statement:
--   Let $n = 4m$ with $m \ge 2$ (so $n > 4$), let $\rho$ be uniform on $S_n$, and deal $(2m, m; m)$: Alice gets the cards at positions $0,\dots,2m-1$, Bob those at positions $2m,\dots,3m-1$, and $m$ cards are discarded. Run the Multi Tetrahedral Protocol (Fig. 31): announce the rank-count sets, and run the Tetrahedral Protocol on every rank of the good set $G(\rho)$, the party holding two cards of the rank acting as sender. Then:
--
--   1. (correctness and security) for every $m\ge 2$ the protocol perfectly realizes the ideal functionality ½ROT$_g$ against semi-honest parties: the outputs are, given the role map, independent random 1-of-2 oblivious transfers on the ranks of $G(\rho)$, and some simulator that sees only one party's ideal output reproduces the joint law of that party's view (its whole ordered hand and the whole public transcript) and both outputs;
--   2. (yield) as $m\to\infty$,
--   $$\mathbb E[g(\rho)] = \Theta(n).$$
--
--   Running many Tetrahedral instances in parallel on one shuffle of a large deck thus gives a linear number of perfectly secure oblivious transfers.
--
--   **Formalization Note** Correctness and security hold for every $m\ge 2$, not only asymptotically. The yield claim is a big-$\Theta$ statement along $m\to\infty$ comparing $m\mapsto\mathbb E[g(\rho)]$ with $m\mapsto 4m = n$.
--
--   Differences from the source:
--   - reading: "securely against semi-honest adversaries" / "perfectly secure against semi-honest adversaries" / "information-theoretically secure for honest-but-curious parties" (§2: "perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations") → the published TetraOT.PerfectSemiHonestRealizes: equal output laws, and for each party a simulator seeing only that party's ideal output that reproduces the joint law of (view, both outputs); reason: the notion §2 names and the one the live mission's Theorem 4.1 uses; perfect and standalone
--   - reading: the parties' views → each party's view is its whole ordered hand and the whole public transcript (S_A(ρ,2), S_A(ρ,1), S_B(ρ,1), S_B(ρ,2) and every M_r); reason: this is everything a party sees in Fig. 31
--   - reading: correct; Out: g(ρ), {P_A(ρ, r)} (Fig. 31); ½ROT_g → outputs are the role map (who sends at each rank, none off G(ρ); it determines g(ρ)) and the per-rank results; the ideal law idealMulti draws the role map from its real law and independent uniform ROT bits per rank, oriented by role; reason: G(ρ) is common knowledge (p.12) and the paper's privacy claim is that the distribution for any successful r is uniform regardless of the other ranks (§10.3)
--   - reading: run the single instance Tetrahedral Protocol on each r ∈ G(ρ), including the (1,2;1) ranks → the two-card party is the sender and applies A to the suits of its two rank-r cards in position order; the one-card party applies B to M_r and its suit; reason: the per-rank instance of p.11–12, with the reversed (1,2;1) case as on p.11
--   - reading: the four cards of rank r are 'mapped in the natural isomorphic way from {0,1,2,3}' (suits assigned arbitrarily) → suit of card x is x / m; reason: one fixed choice of the arbitrary suit assignment; the claims hold for every fixed choice
--   - encoding: Bob's result (y₀, y₁) ∈ {0•, 1•, •0, •1} → the pair (s, m_s) of Booleans, true = 1; reason: one-to-one recoding (right dot = s = 0, Fig. 5 caption), as in the published bobTable
--   - encoding: n = 4m > 4 → m : ℕ with 2 ≤ m, deck Fin (4 * m); reason: 4m > 4 iff m ≥ 2; same instances
--   - reading: Θ(n) for the expected yield → IsTheta atTop of m ↦ 𝔼[g] against m ↦ 4m; reason: n = 4m ranges over the multiples of 4, so Θ(n) is the asymptotic in m; the proof's '→ 9/32 n' (p.13) is a slip (the ratio to n tends to 9/128) and is not part of the theorem
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 10.1, p.12, with §10 and Fig. 31, pp.11–12 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes
import Definitions.Def_TetraOT_Supplement_multiRun
import Definitions.Def_TetraOT_Supplement_idealMulti
import Definitions.Def_TetraOT_Supplement_expectedYield

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT Asymptotics Filter

/-- **Theorem 10.1 (Multi Tetrahedral Protocol on `S_n`)** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 10.1, p.12, with §10 and Fig. 31,
pp.11–12; p. = PDF page, the PDF has no printed page numbers): "Let n = 4m > 4 and let ρ ←$ S_n be
distributed uniformly. The Multi Tetrahedral Protocol is correct, information-theoretically secure for
honest-but-curious parties, and it provides 𝔼[g(ρ)] = Θ(n) instances of ½ROT."

The deck is `{0, …, 4m − 1}`; `ρ` is uniform on `S_{4m}`; Alice holds the cards at positions
`0, …, 2m − 1`, Bob those at positions `2m, …, 3m − 1`, and the remaining `m` are discarded (a
`(2m, m; m)` deal). Card `x` has rank `x mod m` and suit `x / m`. The parties announce
`S_A(ρ, 2), S_A(ρ, 1), S_B(ρ, 1), S_B(ρ, 2)` and run the Tetrahedral Protocol on every rank of
`G(ρ) = (S_A(ρ,2) ∩ S_B(ρ,1)) ∪ (S_A(ρ,1) ∩ S_B(ρ,2))`, the two-card party acting as sender. Then:
1. for every `m ≥ 2` (`n = 4m > 4`), the protocol perfectly realizes the ideal functionality
   ½ROT_g (`idealMulti`) against a semi-honest Alice and a semi-honest Bob, with each party's view its
   whole ordered hand plus the whole public transcript: the outputs are, given the role map, independent
   uniform 1-of-2 random oblivious transfers on the ranks of `G(ρ)` (correctness), and each party's
   view can be simulated from its own ideal output alone (security);
2. the expected yield is linear in `n`:
$$\mathbb E[g(\rho)] = \Theta(n) \quad (m \to \infty).$$

**Formalization Note.** Security and correctness are stated for every `m ≥ 2`, not asymptotically; only
the yield claim is asymptotic, as `Asymptotics.IsTheta` along `atTop` of `m ↦ 𝔼[g]` against
`m ↦ 4m = n`. The proof's "→ 9/32 n" (p.13) is not part of the theorem and is not stated. -/
theorem theorem_10_1 :
    (∀ m : ℕ, 2 ≤ m →
      PerfectSemiHonestRealizes (multiDeal m)
        (multiViewA m (2 * m) m (by omega)) (multiViewB m (2 * m) m (by omega))
        (multiAliceOut m (2 * m) m (by omega)) (multiBobOut m (2 * m) m (by omega))
        (idealMulti m (2 * m) m (by omega))) ∧
    (fun m : ℕ => expectedYield m (2 * m) m (by omega)) =Θ[atTop] (fun m : ℕ => (4 * m : ℝ)) := by sorry

end TetraOT.Supplement
