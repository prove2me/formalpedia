-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_proposition_12_samples
-- name    : SecretaryAdvice.Samples.proposition_12_samples
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:23.649914+00:00
-- url     : https://prove2.me/theorems/d75197cd-94dd-4388-95e8-1f51fd96af29
-- title:
--   Proposition 12, p. 13, for the samples LP — greedy dual optimal and monotone ⇒ an optimal primal solution has threshold shape
-- statement:
--   Let $n\ge1$ and $k\ge0$. Suppose the greedy solution $u$ of (8) for the samples LP is an optimal dual solution and $u(i,s)$ is non-decreasing in $i$ for every $s\in\{0,\dots,k\}$. Then there are a threshold function $t:\{0,\dots,k\}\to[n]$ and an optimal solution $z$ of the samples primal LP with
--   $$z(i,s)=0\ \ (i<t(s)),\qquad z(i,s)=1-\sum_{j<i}\sum_{s'\le s}z(j,s')\,c(i,s,j,s')\ \ (i\ge t(s)).$$
--
--   This is Proposition 12 for the samples LP, in the LP form its proof establishes. Combined with Proposition 10 (part 2) it says that the threshold policy for $t$ is optimal.
--
--   **Formalization Note** "The optimal policy is a threshold policy" is stated through the LP: an optimal primal solution of threshold shape with $1\le t(s)\le n$. The step from that to a policy is `proposition_10_samples`, and the step from policies to the LP is `proposition_9_samples`. NF and HI of the samples model are the items `samples_nf` and `samples_hi`.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 13, Proposition 12 and its proof (with the samples coefficients of p. 15)

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting
import Definitions.Def_SecretaryAdvice_Samples_LP
open Finset

namespace SecretaryAdvice.Samples

theorem proposition_12_samples (n k : ℕ) (hn : 1 ≤ n)
    (hopt : DualFeasible n k (greedyU n k) ∧
      ∀ u : ℕ → ℕ → ℝ, DualFeasible n k u → dualObj n k (greedyU n k) ≤ dualObj n k u)
    (hmono : ∀ s, s ≤ k → ∀ i, 1 ≤ i → i < n → greedyU n k i s ≤ greedyU n k (i + 1) s) :
    ∃ t : ℕ → ℕ, ValidThreshold n k t ∧
      ∃ z : ℕ → ℕ → ℝ, PrimalFeasible n k z ∧
        (∀ z' : ℕ → ℕ → ℝ, PrimalFeasible n k z' → primalObj n k z' ≤ primalObj n k z) ∧
        ThresholdShaped n k t z := by sorry

end SecretaryAdvice.Samples
