-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_3_2
-- name    : SupplyRevenue.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:16.74819+00:00
-- url     : https://prove2.me/theorems/294e03c6-dfff-487f-9834-4a71231c158b
-- title:
--   Lemma 3.2 — lattice demand
-- statement:
--   Let $v$ be a normalized monotone supermodular value and $p$ a price vector.
--
--   1. If $p>0$, then on each assortment the utility-then-payment optimizer is unique. If $S\subseteq A$, $X$ is the optimizer on $A$ and $Q$ on $S$, then $Q\subseteq X$; and if $X\subseteq S$ then $Q=X$.
--   2. If $p\ge 0$, the utility/payment optimizers on $A$ are closed under union and intersection. There is an optimizer $Y$ contained in every optimizer and in every source demand, and $Y$ is the unique optimizer of minimum cardinality.
--
--   This is the structure that controls source-coordinate allocation in the $\mathcal S_r$ row, with no knowledge of the partition.
--
--   Differences from the source:
--   - encoding: "form a lattice" → closure under union and intersection; reason: same meaning for families of subsets
--   - encoding: "source demand" → the tie-ruled demand at offer $(A,p)$ for every rank; reason: the rank is the fixed residual order
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 3.2, p.7

import Mathlib
import Definitions.Def_SupplyRevenue_Local

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 3.2, p.7 (Lattice demand).

**Formalization Note** `A` is the assortment on which the buyer has full stock, and `S ⊆ A` the stock after deletion.
Positive prices: the utility-then-payment optimizer is unique, it shrinks after deletion, and it is retained if the
full-stock set survives. Nonnegative prices: the optimizers on `A` are closed under union and intersection, and there is
a minimum member `Y`, contained in every optimizer and in every tie-ruled source demand, and the unique optimizer of
minimum cardinality. -/
theorem lemma_3_2 {m : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsValuation v)
    (hsuper : ∀ A B, v A + v B ≤ v (A ∪ B) + v (A ∩ B)) (p : Fin m → ℝ) :
    ((∀ j, 0 < p j) →
      (∀ A, ∃! Q, IsUtilPayOpt v p A Q) ∧
      ∀ A S X Q, S ⊆ A → IsUtilPayOpt v p A X → IsUtilPayOpt v p S Q →
        Q ⊆ X ∧ (X ⊆ S → Q = X)) ∧
    ((∀ j, 0 ≤ p j) → ∀ A,
      (∀ X Y, IsUtilPayOpt v p A X → IsUtilPayOpt v p A Y →
        IsUtilPayOpt v p A (X ∪ Y) ∧ IsUtilPayOpt v p A (X ∩ Y)) ∧
      ∃ Y, IsUtilPayOpt v p A Y ∧ (∀ X, IsUtilPayOpt v p A X → Y ⊆ X) ∧
        (∀ (tie : Tie m) (o : Offer m), o.assort = A → o.price = p →
          Y ⊆ demand tie v o Finset.univ) ∧
        ∀ X, IsUtilPayOpt v p A X → X.card ≤ Y.card → X = Y) := by sorry

end SupplyRevenue
