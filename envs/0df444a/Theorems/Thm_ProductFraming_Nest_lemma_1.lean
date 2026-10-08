-- Prove2me | Theorems.Thm_ProductFraming_Nest_lemma_1
-- name    : ProductFraming.Nest.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:01.632607+00:00
-- url     : https://prove2.me/theorems/7aa28e29-0294-4764-bdfe-9220574bb56e
-- title:
--   Lemma 1 — removing one product does not lower per-product revenue
-- statement:
--   Let $P$ be a choice model satisfying Assumption A1 and let the revenues be nonnegative, $r_i\ge0$. For every set $S\subseteq[n]$ with $|S|\ge2$ there is a product $i\in S$ such that
--   $$\frac{\sum_{k\in S,\,k\ne i}r_kP(k,S\setminus\{i\})}{|S|-1}\ \ge\ \frac{\sum_{k\in S}r_kP(k,S)}{|S|},$$
--   that is, $R(S\setminus\{i\})/(|S|-1)\ge R(S)/|S|$.
--
--   The paper cites this result from Davis, Topaloglu and Williamson (2015). It guarantees that step 2 of NEST($y$) can always be carried out.
--
--   **Formalization Note** The hypothesis $r_i\ge0$ is added: the paper speaks of unit revenues, and the lemma fails for negative ones (for $S=\{1,2\}$, $P(k,S)=1/3$, $P(k,\{k\})=1/2$, $r=(-1,-1)$ the left side is $-1/2$ and the right side $-1/3$). $S\setminus\{i\}$ is `S.erase i`, and cardinalities are cast to $\mathbb R$ before subtracting.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 8, Lemma 1 (Davis et al. 2015)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset

/-- Lemma 1 (Davis et al. 2015; Gallego, Li, Truong, Wang 2020, p. 8): for any `S` with `|S| ≥ 2`
there is `i ∈ S` with `R(S \ {i}) / (|S| − 1) ≥ R(S) / |S|`. The hypothesis `0 ≤ r` is added
(the lemma fails for negative revenues). -/
theorem lemma_1 (n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (P : Fin n → Finset (Fin n) → ℝ)
    (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ i ∈ S, R r P S / (S.card : ℝ) ≤ R r P (S.erase i) / ((S.card : ℝ) - 1) := by sorry

end ProductFraming.Nest
