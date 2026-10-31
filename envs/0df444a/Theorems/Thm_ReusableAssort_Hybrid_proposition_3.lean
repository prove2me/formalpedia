-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_proposition_3
-- name    : ReusableAssort.Hybrid.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:31.909735+00:00
-- url     : https://prove2.me/theorems/bdd0d507-0e9a-4566-8ee2-45b5b0b912f9
-- title:
--   Proposition 3, p. 13 — sub-assortment sampling returns S̃ ⊆ S with E[ϕ(S̃, i)] = p_i
-- statement:
--   Let $\phi$ be a choice model on a collection $\mathcal S$ of assortments that is weakly substitutable ($\phi(\emptyset, i) = 0$ and $\phi(S \cup \{j\}, i) \le \phi(S, i)$ whenever $S, S \cup \{j\} \in \mathcal S$, $j \ne i$) and downward closed, with $\phi(S, \cdot)$ a sub-probability supported on $S$ for each $S \in \mathcal S$. Let $S \in \mathcal S$ and let $\{p_i\}_{i \in S}$ satisfy $0 \le p_i \le \phi(S, i)$. Then Procedure 1 run on $(\phi, S, p)$ outputs a random assortment $\tilde S$ such that:
--   1. $\tilde S \subseteq S$;
--   2. its law is a probability distribution on the subsets of $S$;
--   3. for every $i \in S$,
--   $$\mathbb E_{\tilde S}\big[\phi(\tilde S, i)\big] = p_i .$$
--
--   This is the post-processing guarantee of the paper: after products have been discarded, the offered set restores the choice probability of every surviving product to its target, whatever was discarded. It is what lets the analysis treat each product separately.
--
--   **Formalization Note** $p_i \ge 0$ is added (targets are probabilities). The page's claim that the procedure runs in time $\mathrm{Poly}(n)$ is not formalized. Clause 2 is implicit on the page (the procedure is a sampler) and is stated so that clause 3 is an expectation under a genuine distribution.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 13, Proposition 3

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_SubAssort

namespace ReusableAssort.Hybrid

theorem proposition_3 {n : ℕ} (φ : Finset (Fin n) → Fin n → ℝ)
    (feas : Finset (Finset (Fin n)))
    (h_empty : ∀ i, φ ∅ i = 0)
    (h_subst : ∀ S ∈ feas, ∀ i j, j ≠ i → insert j S ∈ feas → φ (insert j S) i ≤ φ S i)
    (h_down : ∀ S ∈ feas, ∀ S' ⊆ S, S' ∈ feas)
    (h_nonneg : ∀ S ∈ feas, ∀ i, 0 ≤ φ S i)
    (h_supp : ∀ S ∈ feas, ∀ i, i ∉ S → φ S i = 0)
    (h_sum : ∀ S ∈ feas, ∑ i ∈ S, φ S i ≤ 1)
    (S : Finset (Fin n)) (hS : S ∈ feas)
    (p : Fin n → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i ∧ p i ≤ φ S i) :
    (∀ U, subAssort φ S p U ≠ 0 → U ⊆ S) ∧
    (∀ U, 0 ≤ subAssort φ S p U) ∧
    ∑ U ∈ S.powerset, subAssort φ S p U = 1 ∧
    ∀ i ∈ S, ∑ U ∈ S.powerset, subAssort φ S p U * φ U i = p i := by sorry

end ReusableAssort.Hybrid
