-- Prove2me | Theorems.Thm_PrivLearn_Parity_solution_space_halving
-- name    : PrivLearn.Parity.solution_space_halving
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:11.663245+00:00
-- url     : https://prove2.me/theorems/35c15b81-74c8-4a48-b92f-c31e9c3fc14e
-- title:
--   Proof of Claim 4.3, p. 16 — one consistent equation at most halves the solution space
-- statement:
--   Let $z = ((x_1,y_1),\dots,(x_n,y_n))$ be any database of labeled examples in $\{0,1\}^d \times \{0,1\}$, let $T \subseteq [n]$ and $i \in [n]$, and let $V_S$ be the set of solutions $r \in \mathbb Z_2^d$ of $\{x_j \odot r = y_j : j \in S\}$. If $V_{T \cup \{i\}} \neq \emptyset$, then
--
--   $$
--   |V_T| \le 2\, |V_{T \cup \{i\}}|.
--   $$
--
--   Over $\mathbb Z_2$, a consistent linear constraint either halves the solution space or leaves it unchanged. This is the step that bounds by $2$ the ratio in Claim 4.3, and hence the privacy loss of $\mathcal A$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 16, proof of Claim 4.3, display

import Mathlib
import Definitions.Def_PrivLearn_Parity_Learner

namespace PrivLearn.Parity

/-- Proof of Claim 4.3, p. 16: over `ℤ₂`, adding one consistent linear constraint to a system at
most halves its solution space: if `V_{T ∪ {i}} ≠ ∅` then `|V_T| ≤ 2 |V_{T ∪ {i}}|`, for every
database `z` (consistent or not), every `T ⊆ [n]` and every `i ∈ [n]`. -/
theorem solution_space_halving {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (h : (solSpace z (insert i T)).Nonempty) :
    (solSpace z T).card ≤ 2 * (solSpace z (insert i T)).card := by sorry

end PrivLearn.Parity
