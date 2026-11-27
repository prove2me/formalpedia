-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_16
-- name    : SampleMechDesign.Supplement.theorem_A_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:53:29.784139+00:00
-- url     : https://prove2.me/theorems/c7af56db-2ab8-42c8-98b3-7d8b1f392ba5
-- title:
--   Theorem A.16 — sample-complexity lower bounds: $N_{\mathcal M}(\epsilon,\delta)\ge(n^m-n)/2$ for AMAs and λ-auctions, $\ge2^m-2$ for VVCAs
-- statement:
--   For a class of auctions $\mathcal M$, let $N_{\mathcal M}(\epsilon,\delta)$ be the number of samples required to ensure that for any distribution $\mathcal D$, with probability at least $1-\delta$ over the draw of a sample of size $N_{\mathcal M}(\epsilon,\delta)$ from $\mathcal D$, every auction $M\in\mathcal M$ has average profit $\epsilon$-close to its expected profit. Then, for every $\epsilon>0$, $\delta\in(0,1)$, $n\ge1$ buyers and $m$ items, with zero cost:
--
--   1. if $\mathcal M$ is the set of AMAs or the set of λ-auctions, $\displaystyle N_{\mathcal M}(\epsilon,\delta)\ \ge\ \frac{n^m-n}{2}$;
--   2. if $\mathcal M$ is the set of VVCAs, $\displaystyle N_{\mathcal M}(\epsilon,\delta)\ \ge\ 2^m-2$.
--
--   "$N_{\mathcal M}(\epsilon,\delta)\ge B$" means that whenever $N$ samples suffice for $\mathcal M$, $N\ge B$. The classes act on additive valuation vectors and only finitely supported distributions are required, which makes the lower bounds stronger. The bounds hold for every tie-breaking rule.
--
--   Together with Lemma 3.20 this shows that exponentially many samples are both sufficient and necessary for these auction classes.
--
--   Differences from the source:
--   - reading: the cost function (general unless noted) → zero cost; reason: the constructions of Theorems A.17 and A.21 use zero cost (the paper's lower-bound instance); the paper gives no argument for other cost functions
--   - generalization: "for any distribution D" over valuation vectors → the sample-size hypothesis is only required for finitely supported distributions over additive valuation vectors; reason: a weaker hypothesis gives a stronger lower bound; the paper notes the bound holds even for additive valuations (p.36)
--   - reading: the tie-breaking rule is not specified → every tie-breaking rule; reason: the paper leaves ties open
--   - reading: n buyers and every ε, δ → 1 ≤ n, ε > 0, δ ∈ (0, 1); reason: with no buyer every profit is 0 and no sample is needed, while 0^0 − 0 = 1 and 2^m − 2 > 0 for m ≥ 2
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.16, p.34 (PDF p.34); Theorems A.17, A.20, A.21, pp.34–37

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_vvcaBoost
import Definitions.Def_SampleMechDesign_Supplement_SamplesSuffice

namespace SampleMechDesign.Supplement

/-- **Theorem A.16.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.34. For a class of
auctions `M`, let `N_M(ε, δ)` be the number of samples required to ensure that for any
distribution `D`, with probability at least `1 − δ` over a sample of that size, every auction in
`M` has average profit `ε`-close to expected profit. Then

1. if `M` is the set of AMAs or of λ-auctions, `N_M(ε, δ) ≥ (n^m − n)/2`;
2. if `M` is the set of VVCAs, `N_M(ε, δ) ≥ 2^m − 2`.

"`N_M(ε, δ) ≥ B`" is written as: every `N` for which `N` samples suffice (`SamplesSuffice`) has
`N ≥ B`.

**Formalization Note.**
* Zero cost, as in the constructions of Theorems A.17 and A.21, which ignore the cost (the paper's
  lower-bound instance; it gives no argument for other cost functions).
* The classes act on additive valuation vectors ("this holds even when the bidders' valuation
  functions are additive", p.36), and `SamplesSuffice` only asks for finitely supported
  distributions; both make the hypothesis weaker and the lower bound stronger.
* Every `ε > 0`, every `δ ∈ (0, 1)`, every tie-breaking rule `tb`.
* `1 ≤ n`: with no buyer every profit is `0` and no sample is needed, while `0^0 − 0 = 1` and
  `2^m − 2 > 0` for `m ≥ 2`. Part 2 is stated for every `n ≥ 1`, including `n = 1`, which the
  paper's two-bidder construction does not cover. -/
theorem theorem_A_16 {n m : ℕ} (hn : 1 ≤ n) (tb : BVal n m → Finset (Alloc n m) → Alloc n m)
    (htb : IsChoice tb) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) (N : ℕ) :
    (SamplesSuffice (amaAdditiveClass (fun _ => 0) tb) ε δ N →
        ((n : ℝ) ^ m - n) / 2 ≤ N) ∧
    (SamplesSuffice (lambdaAuctionClass (fun _ => 0) tb) ε δ N →
        ((n : ℝ) ^ m - n) / 2 ≤ N) ∧
    (SamplesSuffice (vvcaClass (fun _ => 0) tb) ε δ N → (2 : ℝ) ^ m - 2 ≤ N) := by sorry

end SampleMechDesign.Supplement
