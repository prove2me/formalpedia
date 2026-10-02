-- Prove2me | Theorems.Thm_ServiceParts_Allocation_eppen_schrage_balance
-- name    : ServiceParts.Allocation.eppen_schrage_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:08:26.242389+00:00
-- url     : https://prove2.me/theorems/65c8637e-b461-453f-ac5a-804f04e15c8b
-- title:
--   Lemma 3 — a balanced system stays balanced after the depot allocation
-- statement:
--   Consider the depot/warehouse system of Section 7.2.1 with $m$ warehouses, depot-to-warehouse lead time $A \ge 1$ periods, and demand parameters $\mu_j$ and $\sigma_j > 0$. Inventory positions $I_1, \dots, I_m$ are **in balance** when $\Phi\bigl((I_j - A\mu_j)/(\sqrt A\,\sigma_j)\bigr)$ is the same for every $j$, $\Phi$ the standard normal distribution function.
--
--   Suppose the system is in balance at the beginning of period $t + D - 1$, with positions $I_{j,t+D-1}$. The depot receives $\sum_j d_{j,t-1}$ units, allocates $x_j$ of them to warehouse $j$, and demands $d_{j,t+D-1}$ occur, so that $I_{j,t+D} = I_{j,t+D-1} + x_j - d_{j,t+D-1}$. If
--   $$\sum_{j=1}^m d_{j,t-1} \;\ge\; \max_{i=1,\dots,m} \Bigl\{ \sum_{j \ne i} d_{j,t+D-1} + d_{i,t+D-1} \Bigl(1 - \frac{\sum_j \sigma_j}{\sigma_i}\Bigr) \Bigr\},$$
--   then there are $x_j \ge 0$ with $\sum_j x_j = \sum_j d_{j,t-1}$ for which the positions $I_{j,t+D}$ are again in balance.
--
--   The lemma is the basis for estimating how likely the imbalance assumption of the Eppen–Schrage analysis is to hold.
--
--   **Formalization Note** The statement is deterministic: the demands are arbitrary real numbers (normal demand can be negative). The maximum over $i$ is written as the inequality for every $i$. The lemma is stated as a sufficient condition, as in the book.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 152, Lemma 3 (proof pp. 153-154)

import Mathlib
import Definitions.Def_ServiceParts_Allocation_PoolingSystem

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Lemma 3, p. 152 (Eppen–Schrage): if the inventory positions
`I_j = I_{j,t+D-1}` are in balance, then the depot can allocate all `Σ_j d_{j,t-1}` units it
receives, in nonnegative amounts `x_j`, so that the new positions
`I_{j,t+D} = I_{j,t+D-1} + x_j - d_{j,t+D-1}` are in balance, provided
`Σ_j d_{j,t-1} ≥ max_i { Σ_{j≠i} d_{j,t+D-1} + d_{i,t+D-1} (1 - Σ_j σ_j / σ_i) }`.
Here `dPrev j = d_{j,t-1}` and `dNow j = d_{j,t+D-1}`. -/
theorem eppen_schrage_balance {m : ℕ} (A : ℕ) (hA : 0 < A) (μ σ : Fin m → ℝ)
    (hσ : ∀ j, 0 < σ j) (I dPrev dNow : Fin m → ℝ) (hbal : InBalance A μ σ I)
    (hcond : ∀ i, (∑ j ∈ Finset.univ.erase i, dNow j) + dNow i * (1 - (∑ j, σ j) / σ i)
      ≤ ∑ j, dPrev j) :
    ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j, x j = ∑ j, dPrev j ∧
      InBalance A μ σ (fun j => I j + x j - dNow j) := by sorry

end ServiceParts.Allocation
