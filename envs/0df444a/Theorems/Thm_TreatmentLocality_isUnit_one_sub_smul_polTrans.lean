-- Prove2me | Theorems.Thm_TreatmentLocality_isUnit_one_sub_smul_polTrans
-- name    : TreatmentLocality.isUnit_one_sub_smul_polTrans
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:21.108921+00:00
-- url     : https://prove2.me/theorems/78fa336b-b300-4828-94df-c147c17be7d9
-- title:
--   Invertibility of the discounted Bellman system $I-\gamma P^a$
-- statement:
--   **The Bellman system of a discounted Markov decision process is invertible.** For the SST model of arXiv:2407.19618, let $P^a$ be the transition matrix of the policy that plays arm $a$ and $\gamma \in [0,1)$ the discount factor. Then $I - \gamma P^a$ is a unit in the ring of matrices.
--
--   The proof is the standard contraction argument made precise: in the $L^\infty$ operator norm the norm of a matrix is the largest absolute row sum, and the rows of $P^a$ are probability vectors, so $\|\gamma P^a\| = \gamma < 1$. In a complete normed ring an element within distance $1$ of the identity is invertible, its inverse being the Neumann series $\sum_{k\ge 0} \gamma^k (P^a)^k$ — which is exactly the discounted occupancy measure. This is the fact that makes the closed form $V^a = (I - \gamma P^a)^{-1} r^a$ of the policy value legitimate, and hence the model-based plug-in estimator well defined.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2, eq. (2) (the discounted value function V^a = (I - gamma P^a)^{-1} r^a of the SST model). See also M. L. Puterman, Markov Decision Processes, Wiley 1994, Theorem 6.1.1.

import Definitions.Def_TreatmentLocality

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.isUnit_one_sub_smul_polTrans {S : Type*} [DecidableEq S]
    [Fintype S] (M : Model S) (a : Bool) :
    IsUnit ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) := by sorry
