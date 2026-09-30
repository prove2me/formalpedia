-- Prove2me | Theorems.Thm_SupplyChainTheory_flex_supermodular_expected
-- name    : SupplyChainTheory.flex_supermodular_expected
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:11:54.376497+00:00
-- url     : https://prove2.me/theorems/3400e2f7-7ff7-4151-b8cc-2da463afb636
-- title:
--   Corollary 7.6: $[E] + [E \setminus \{\alpha, \beta\}] \ge [E \setminus \{\alpha\}] + [E \setminus \{\beta\}]$
-- statement:
--   **Corollary 7.6.** Let $E \subseteq C_n$ be a flexibility design for a balanced system of size
--   $n$ and let $\alpha$ and $\beta$ be two flexible edges in $E$. Then, with
--   $[E] = \mathbb{E}[P(D, E)]$ the expected performance over the random demand $D$,
--
--   $$ [E] + [E \setminus \{\alpha, \beta\}] \;\ge\; [E \setminus \{\alpha\}] + [E \setminus \{\beta\}]. $$
--
--   Since Lemma 7.5 holds for every demand realization it holds in expectation: any two flexible
--   edges of the long chain complement each other, having one increasing the marginal benefit of
--   adding the other. Exchangeability is not needed here; it enters in Lemma 7.7.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 250, Sect. 7.5.3, Corollary 7.6, Eq. (7.28)

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem flex_supermodular_expected {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (E : Finset (Fin n × Fin n)) (hE : E ⊆ longChain n)
    (a b : Fin n × Fin n) (ha : a ∈ E) (hb : b ∈ E) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b) :
    S.expPerf (E \ {a}) + S.expPerf (E \ {b}) ≤ S.expPerf E + S.expPerf (E \ {a, b}) := by sorry

end SupplyChainTheory
