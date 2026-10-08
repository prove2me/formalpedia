-- Prove2me | Theorems.Thm_PariMutuel_Consensus_exists_isPhiMaximizer
-- name    : PariMutuel.Consensus.exists_isPhiMaximizer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:22:17.995491+00:00
-- url     : https://prove2.me/theorems/089f32fb-7a1c-4781-bbd3-48a401d98244
-- title:
--   p. 167 — $\varphi$ attains its maximum on $D$, with positive inner sums
-- statement:
--   Let $P=(p_{ij})$ and $b$ define a pari-mutuel market (rows of $P$ are probability distributions, every column has a positive entry, $b_i>0$, $\sum_i b_i=1$), and let $\varphi(\xi)=\sum_i b_i\log\sum_j p_{ij}\xi_{ij}$ on the domain $D=\{\xi:\ \xi_{ij}\ge 0,\ \sum_i\xi_{ij}=1\ \forall j\}$. Then there is a point $\bar\xi\in D$ with
--
--   $$
--   \sum_{j=1}^n p_{ij}\bar\xi_{ij}>0\ \text{ for every } i,\qquad \varphi(\eta)\le\varphi(\bar\xi)\ \text{ for every } \eta\in D \text{ with all inner sums positive}.
--   $$
--
--   This is the starting point of the variational existence proof: the equilibrium is read off from such a maximizer.
--
--   **Formalization Note** The paper extends $\varphi$ by $-\infty$ where an inner sum vanishes; here the comparison is restricted to points of $D$ with positive inner sums, which is equivalent.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 167, first paragraph after the definition of φ

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem exists_isPhiMaximizer {m n : ℕ} (M : Market m n) : ∃ ξ, M.IsPhiMaximizer ξ := by sorry
end PariMutuel.Consensus
