-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_11_nonneg
-- name    : ProductMixAuction.Allocate.lemma_11_nonneg
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T15:40:40.681811+00:00
-- url     : https://prove2.me/theorems/5622e3f2-e9c9-42ed-96e9-4824478449d7
-- title:
--   Lemma 11 (with non-negative partial allocations), p. 19 — NonMarginals returns a valid reduction and keeps G_A
-- statement:
--   Let $A=[p,(\mathcal B^j)_{j\in J},(m^j)_{j\in J},r]$ be an allocation problem in the sense of Definition 4 (p. 15), and let
--   $$A'=\mathrm{NonMarginals}(A)=[p,(\mathcal B'^j),(m'^j),r']$$
--   be the output of Algorithm 3 (p. 19). Every bid $b$ that is non-marginal at $p$ is removed from its list, and its weight $w(b)$ is added to $m^j_i$ and subtracted from $r_i$, where $i$ is the unique good $b$ demands. Suppose the new partial allocations are non-negative:
--   $$m'^j_i\ \ge\ 0\qquad\text{for all } j\in J,\ i\in[n]_0 .$$
--   Then $A'$ is a valid reduction of $A$ (Definition 5): $A'$ is an allocation problem and every solution of $A'$ is a solution of $A$. Moreover, $A$ and $A'$ have the same marginal bids graph, $G_{A'}=G_A$ (Definition 6).
--
--   This is Lemma 11 of the paper with the proviso $m'\ge0$ added. Without it the statement is false. When a list is only locally valid, accepting a non-marginal bid of weight $-1$ can make a partial allocation negative, and $A'$ is then not an allocation problem. The milestone `ProductMixAuction.Allocate.lemma_11` has been disproved by exactly such an example. Inside Allocate the proviso always holds: at the initial problem because the lists are globally valid, after UnambiguousMarginals because no non-marginal bids remain, and after ShiftProjectUnshift by the companion statement `ProductMixAuction.Allocate.lemma_18_nonMarginals_nonneg`.
--
--   **Formalization Note** `nonMarginals`, `IsReduction` and `edges` are those of the mission definitions. The proviso is stated on the output's partial allocations, `(nonMarginals A).m`.
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 19, Lemma 11 and Algorithm 3 (NonMarginals); allocation problem and valid reduction, Definitions 4-5, pp. 15-16 (m^j in Z_+^{n+1})

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_11_nonneg {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A) (hm : ∀ j k, 0 ≤ (nonMarginals A).m j k) :
    IsReduction (nonMarginals A) A ∧ edges (nonMarginals A) = edges A := by sorry

end ProductMixAuction.Allocate
