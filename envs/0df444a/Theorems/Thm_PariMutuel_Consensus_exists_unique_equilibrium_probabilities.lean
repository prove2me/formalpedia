-- Prove2me | Theorems.Thm_PariMutuel_Consensus_exists_unique_equilibrium_probabilities
-- name    : PariMutuel.Consensus.exists_unique_equilibrium_probabilities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:03:44.571973+00:00
-- url     : https://prove2.me/theorems/76c8ab5e-1e9c-401a-be5d-f6a32e96933e
-- title:
--   Equilibrium track probabilities of a pari-mutuel market exist and are unique
-- statement:
--   Let $m$ bettors and $n$ horses form a pari-mutuel market: an $m\times n$ subjective probability matrix $P=(p_{ij})$ whose rows are probability distributions and whose columns each contain a positive entry, and budgets $b_i>0$ with $\sum_i b_i=1$. Then there is exactly one vector $\pi=(\pi_1,\dots,\pi_n)$ for which some bets $\beta_{ij}$ make $(\pi,\beta)$ equilibrium probabilities and bets:
--
--   $$
--   \exists!\,\pi\ \ \exists\,\beta:\quad \pi,\beta\ge 0,\quad \sum_j\beta_{ij}=b_i,\quad \sum_i\beta_{ij}=\pi_j,\quad \beta_{ij}>0\Rightarrow \frac{p_{ij}}{\pi_j}=\max_s\frac{p_{is}}{\pi_s}.
--   $$
--
--   This is the announced result of the paper: "such probabilities and bets do exist and ... the probabilities are in fact unique, thus giving a well-defined notion of consensus." The bets need not be unique.
--
--   **Formalization Note** Only $\pi$ is under the unique-existence quantifier; $\beta$ is existential. Condition (3) is multiplied out, $p_{is}\pi_j\le p_{ij}\pi_s$ whenever $\beta_{ij}>0$, which equals the displayed form when $\pi>0$ and reads $p/0=+\infty$ otherwise; positivity of $\pi$ is not assumed.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, pp. 165–166 (announcement), p. 167 EXISTENCE THEOREM, p. 168 UNIQUENESS THEOREM

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem exists_unique_equilibrium_probabilities {m n : ℕ} (M : Market m n) :
    ∃! π : Fin n → ℝ, ∃ β : Fin m → Fin n → ℝ, M.IsEquilibrium π β := by sorry
end PariMutuel.Consensus
