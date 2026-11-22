-- Prove2me | Theorems.Thm_StabilizerRank_stabRank_hState_omega_linear
-- name    : StabilizerRank.stabRank_hState_omega_linear
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T22:03:04.266753+00:00
-- url     : https://prove2.me/theorems/97615fac-adbe-40cb-be02-ec1f62b05f82
-- title:
--   Peleg--Shpilka--Volk: $\chi(|H^{\otimes n}\rangle)=\Omega(n)$
-- statement:
--   The stabilizer rank of the magic-state tensor power grows at least linearly: there are a constant $c>0$ and a threshold $N$ such that
--
--   $$\chi\bigl(|H^{\otimes n}\rangle\bigr)\;\ge\;c\,n \qquad\text{for all } n\ge N .$$
--
--   This is the best unconditional lower bound known for an explicit state, improving an earlier bound of order $\sqrt{n}$. It is the current frontier of the mission's goal: the goal asks for a super-polynomial bound, and this result establishes the linear case. Improving it even to a super-linear bound is known to resolve a separate open question, namely the construction of a Boolean function computable in polynomial time that requires a super-linear number of summands in a decomposition into exponentials of quadratic forms over $\mathbb{F}_2$.
--
--   **Formalization Note** The asymptotic notation $\Omega(n)$ of the source is rendered explicitly as the existence of a positive constant $c$ and a threshold $N$ beyond which the inequality holds, with both quantified outermost. The source states the same bound for the alternative magic state $|R\rangle$; only the $|H\rangle$ case is formalized here.
-- source:
--   S. Peleg, A. Shpilka, B. L. Volk, Lower Bounds on Stabilizer Rank, Quantum 6 (2022) 652; arXiv:2106.03214, Theorem 1.1 (p. 3): "chi(H^{ox n}) = Omega(n), and similarly, chi(R^{ox n}) = Omega(n)". Improving the Omega(sqrt(n)) bound of Bravyi, Smith and Smolin cited there as [7].

import Definitions.Def_StabilizerRank

namespace StabilizerRank

theorem stabRank_hState_omega_linear :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) ≤ (stabRank (hState n) : ℝ) := by sorry

end StabilizerRank
