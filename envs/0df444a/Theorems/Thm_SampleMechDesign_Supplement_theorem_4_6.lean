-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_4_6
-- name    : SampleMechDesign.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:49:06.055439+00:00
-- url     : https://prove2.me/theorems/656b1b7f-e3fc-46d7-b19f-251fa458e7f8
-- title:
--   Theorem 4.6 — item pricing and second-price auctions with reserves have $\mathrm{Pdim}\ge m$ (anonymous) and $\ge nm$ (non-anonymous)
-- statement:
--   Let $\mathcal M$ and $\mathcal M'$ be the classes of anonymous and non-anonymous item-pricing mechanisms with $m$ items and $n\ge1$ buyers. Then
--   $$
--   \mathrm{Pdim}(\mathcal M)\ \ge\ m,\qquad \mathrm{Pdim}(\mathcal M')\ \ge\ nm .
--   $$
--   The same holds if $\mathcal M$ and $\mathcal M'$ are the classes of second-price item auctions with anonymous and non-anonymous reserves.
--
--   Here $\mathrm{Pdim}(F)\ge k$ means that some $k$ valuation vectors are shattered by $F$ (Definition 3.6): there are witnesses $z_1,\dots,z_k$ such that every labelling of the $k$ points is realized by some $f\in F$ through $f(v^{(i)})>z_i$ or $f(v^{(i)})\le z_i$. The statement holds for every cost function, every arrival order and every tie-breaking rule.
--
--   These lower bounds show that the item-independent Rademacher bounds of Lemmas 4.4 and 4.5, which do not depend on the number of items, cannot be obtained from pseudo-dimension alone.
--
--   Differences from the source:
--   - generalization: classes of item-pricing mechanisms and second-price auctions with reserves (price range and valuation domain not specified) → the shattered valuation vectors are additive and the prices or reserves nonnegative; reason: a lower bound for a subclass on a subdomain implies the same bound for every larger price set and valuation domain
--   - reading: the cost function, the arrival order and the tie-breaking rule is not specified → every cost function c, every arrival order ord and every tie-breaking rule; reason: the paper fixes an arbitrary order and leaves ties open; the bound is claimed for all of them
--   - encoding: Pdim(M) ≥ k → some k-tuple of valuation vectors is shattered (published Shatters: label f > z versus f ≤ z); reason: Definition 3.7 defines Pdim as the largest shattered size
--   - reading: n buyers → 1 ≤ n; reason: with no buyer every mechanism has profit −c(∅) and nothing is shattered, so the anonymous bound needs a buyer
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem 4.6, p.16 (PDF p.16); proof p.45; Definitions 3.6–3.7, p.10

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_SampleMechDesign_Supplement_itemPricingProfit
import Definitions.Def_SampleMechDesign_Supplement_secondPriceProfit

namespace SampleMechDesign.Supplement

open FoundationsML.Regression

/-- **Theorem 4.6.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.16 (proof p.45). Let `M`
and `M′` be the classes of anonymous and non-anonymous item-pricing mechanisms. Then
`Pdim(M) ≥ m` and `Pdim(M′) ≥ nm`. The same holds for second-price item auctions with anonymous
and non-anonymous reserves.

"`Pdim(F) ≥ k`" is written as: some `k`-tuple of valuation vectors is shattered by `F`
(Definition 3.6, the published `Shatters`).

**Formalization Note.** The statement holds for every cost function `c`, every arrival order
`ord`, and every tie-breaking rule; the shattered valuation vectors are additive and the prices or
reserves nonnegative, so the bound also holds for any larger class (all real prices, general
valuations). `1 ≤ n`: with no buyer every mechanism has profit `−c(∅)` and nothing is
shattered. -/
theorem theorem_4_6 {n m : ℕ} (hn : 1 ≤ n) (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (htb : IsChoice tb)
    (tbI : AVal n m × Fin m → Finset (Fin n) → Fin n) (htbI : IsChoice tbI)
    (c : Bundles n m → ℝ) :
    (∃ z : Fin m → AVal n m, Shatters (anonItemPricingClass ord tb c) z) ∧
    (∃ z : Fin (n * m) → AVal n m, Shatters (itemPricingClass ord tb c) z) ∧
    (∃ z : Fin m → AVal n m, Shatters (anonSecondPriceClass tbI c) z) ∧
    (∃ z : Fin (n * m) → AVal n m, Shatters (secondPriceClass tbI c) z) := by sorry

end SampleMechDesign.Supplement
