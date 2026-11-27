-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_14
-- name    : SampleMechDesign.Supplement.theorem_A_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:52:43.543127+00:00
-- url     : https://prove2.me/theorems/f6e3a160-7eb9-4041-99a1-4d8fe6663a14
-- title:
--   Theorem A.14 (corrected: the lower bound needs $n,m\ge2$) — mixed bundling auctions have pseudo-dimension exactly 2
-- statement:
--   Let $\mathcal M$ be the class of mixed bundling auctions (γ-MBAs, $\gamma\ge0$). Then $\mathrm{Pdim}(\mathcal M)=2$, in the following sense.
--
--   1. **Upper bound.** For all $n$ and $m$, every cost function and every tie-breaking rule, no $N$ valuation vectors with $N\ge3$ are shattered by $\mathcal M$.
--   2. **Lower bound.** For $n\ge2$ buyers, $m\ge2$ items and zero cost, for every tie-breaking rule there are two valuation vectors shattered by $\mathcal M$.
--
--   Shattering is Definition 3.6 (labels $\mathrm{profit}>z$ versus $\mathrm{profit}\le z$). The paper's construction (Table 5) takes buyers 1 and 2 with value $3$ for at least $\lfloor m/2\rfloor$ items, the second vector adding value $4$ for the grand bundle, and uses $\gamma\in\{0,1.5,1.75,2.5\}$ with witnesses $3$ and $4$.
--
--   With Theorem 3.8 this gives a generalization guarantee for MBAs that depends neither on $n$ nor on $m$.
--
--   Differences from the source:
--   - correction: Pdim(M) = 2 for every n and m → the lower bound Pdim ≥ 2 for n ≥ 2 and m ≥ 2 (the upper bound for all n, m); reason: with m = 1 (⌊m/2⌋ = 0) or n = 1, at zero cost every MBA profit is non-increasing in γ (m = 1: 0 then max(−γ, second-highest gain); n = 1: −λ(Q*)), so no pair is shattered; the construction names buyers 1 and 2
--   - reading: the cost function (general unless noted) → zero cost in the lower bound, every cost function in the upper bound; reason: the proof says "let the cost function be 0"; a lower bound is witnessed by one instance, and the paper gives no argument for other cost functions
--   - reading: the tie-breaking rule is not specified → every tie-breaking rule in both halves; reason: the paper leaves ties open; the statement holds for all of them
--   - encoding: Pdim(M) = 2 → no N-tuple with N > 2 is shattered, and some 2-tuple is shattered (published Shatters); reason: Definition 3.7; the proof's labels ≥ z / < z are translated into Shatters' > z / ≤ z by the choice of witnesses
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.14, p.32 (PDF p.32); Lemma A.15, p.32; Table 5, p.32

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_SampleMechDesign_Supplement_mbaProfit

namespace SampleMechDesign.Supplement

open FoundationsML.Regression

/-- **Theorem A.14.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.32. Let `M` be the class
of mixed bundling auctions. Then `Pdim(M) = 2`. The two halves are:

1. (upper bound) for all `n`, `m`, every cost function and every tie-breaking rule, no `N`-tuple of
   valuation vectors with `N > 2` is shattered by the MBAs;
2. (lower bound) for `n ≥ 2` buyers, `m ≥ 2` items and zero cost, for every tie-breaking rule some
   pair of valuation vectors is shattered.

Shattering is Definition 3.6 (the published `Shatters`: labels `profit > z` versus `profit ≤ z`).

**Formalization Note.**
* Zero cost in the lower bound is the proof's own choice ("let the cost function be 0"): a lower
  bound is witnessed by one instance, and the paper gives no argument for other cost functions.
* `n ≥ 2` and `m ≥ 2` are needed: the construction names buyers 1 and 2, and with `m = 1` (where
  `⌊m/2⌋ = 0`) or with one buyer, at zero cost, every MBA profit is non-increasing in `γ`, so no
  pair is shattered and the pseudo-dimension is at most `1`.
* The valuations are arbitrary functions on bundles (the construction is not additive). -/
theorem theorem_A_14 :
    (∀ (n m : ℕ) (c : Bundles n m → ℝ) (tb : BVal n m → Finset (Alloc n m) → Alloc n m),
      IsChoice tb → ∀ (N : ℕ) (z : Fin N → BVal n m), Shatters (mbaClass c tb) z → N ≤ 2) ∧
    (∀ n m : ℕ, 2 ≤ n → 2 ≤ m → ∀ tb : BVal n m → Finset (Alloc n m) → Alloc n m,
      IsChoice tb → ∃ z : Fin 2 → BVal n m, Shatters (mbaClass (fun _ => 0) tb) z) := by sorry

end SampleMechDesign.Supplement
