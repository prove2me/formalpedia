-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_theorem2_concave_submodular
-- name    : SubstOverbooking.Structure.theorem2_concave_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:36.223317+00:00
-- url     : https://prove2.me/theorems/1e6fa8db-5bf2-49e6-bc08-297071a7e7bf
-- title:
--   Theorem 2, p. 87 — with semigroup survivals, G(u) of (2) is componentwise concave in each uᵢ and submodular in u
-- statement:
--   Consider the overbooking model with $n$ reservation classes, revenues $r_i$ and refunds $q_i \le r_i$, reservations on hand $x_i$, net benefits $a_{ij}$ and capacities $c_j \ge 0$ for the real inventory classes $j = 1, \dots, m$. Suppose that for every class $i$ the survivals $\{Z_i(u_i)\}$ have the semigroup property, with finite means, on a parameter set $P \subseteq [0, \infty)$ (containing $0$, closed under addition and nonnegative differences), and that $Z_1(u_1), \dots, Z_n(u_n)$ are independent. Let $G$ be the expected net revenue (2). Then:
--
--   1. **componentwise concavity (6):** for every $u \in P^n$, every class $i$ and all $\varepsilon, \alpha \in P$,
--   $$G(u + (\varepsilon + \alpha) e_i) - G(u + \alpha e_i) \le G(u + \varepsilon e_i) - G(u);$$
--   2. **submodularity:** for all $u, u' \in P^n$,
--   $$G(u \vee u') + G(u \wedge u') \le G(u) + G(u').$$
--
--   Componentwise concavity yields critical booking levels for each class, and submodularity says these levels are nonincreasing in the bookings accepted for other classes.
--
--   **Formalization Note.** Concavity is stated in the increment form (6), which is what the paper proves and which makes sense on a discrete $P = \mathbb N$ (binomial survivals) as well as on $P = [0, \infty)$ (Poisson survivals). Submodularity is lattice submodularity on $P^n$ via the platform `SupermodularOn` of $-G$. The paper proves the case $n = 2$ and states the extension is straightforward; the statement is for general $n$. The parameter set $P$ is required to be closed under nonnegative differences as well as sums, so that for levels $u_k \le u'_k$ in $P$ the increment $u'_k - u_k$ is again a level and the semigroup property applies to it; the two cases of the paper, $P = \mathbb N$ and $P = [0, \infty)$, have this property.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 87, Theorem 2; proof pp. 87–88, (6)–(8)

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace SubstOverbooking.Structure

theorem theorem2_concave_submodular {n m : ℕ} (r q x : Fin n → ℝ) (hqr : ∀ i, q i ≤ r i)
    (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ) (hc : ∀ j, j ≠ 0 → 0 ≤ c j)
    (P : Set ℝ) (hP : IsParamSet P) (L : Fin n → ℝ → PMF ℕ)
    (hL : ∀ i, IsSemigroupFamily P (L i)) :
    (∀ u : Fin n → ℝ, (∀ k, u k ∈ P) → ∀ i : Fin n, ∀ ε ∈ P, ∀ α ∈ P,
      G r q x a c L (Function.update u i (u i + ε + α)) - G r q x a c L (Function.update u i (u i + α))
        ≤ G r q x a c L (Function.update u i (u i + ε)) - G r q x a c L u) ∧
    Supermodularity.Monotonicity.SupermodularOn (fun u => - G r q x a c L u)
      {u : Fin n → ℝ | ∀ k, u k ∈ P} := by sorry

end SubstOverbooking.Structure
