-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_3
-- name    : PersuasionNetworks.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:04.105147+00:00
-- url     : https://prove2.me/theorems/849e61d1-5973-4285-8848-dd8a8b1f1245
-- title:
--   Lemma 3 — (OPT) is convex and has an optimal solution; lower constraints bind below $\hat k$
-- statement:
--   1. (OPT) is a convex optimization problem: $g$ is concave on $[0,1]$ and the feasible set is convex, with a linear objective.
--
--   2. An optimal solution to (OPT) always exists.
--
--   3. Suppose that $r_k>r_\ell$ for $\ell>k$. For any optimal solution $(p^\star,z^\star)$, with $\hat k=\max\{k\mid p^\star_k>0\}$,
--   $$
--   b_\ell p^\star_\ell=z^\star_\ell\qquad\text{for }\ell<\hat k .
--   $$
--
--   Parts 1 and 2 make (OPT) a well-posed tractable program. Part 3 describes how an optimal solution uses the posterior-mean budget.
--
--   Differences from the source:
--   - reading: (OPT) is a convex optimization problem → g is concave on [0, 1] and the feasible set of pairs (p, z) is convex; reason: the objective is linear by definition; this is the content used on p.40
--   - encoding: k̂ = max{k | p⋆_k > 0} → a bound variable with the defining properties of the maximum; reason: P is nonempty by (O3); same number
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 3, p.17

import Mathlib
import Definitions.Def_PersuasionNetworks_Quantile
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_OPT

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 3**, Candogan, SSRN 3346144 (preprint), p.17 (proof pp.40–41).

1. (OPT) is a convex optimization problem: `g` is concave on `[0, 1]` and the feasible set is convex.
   Its objective is linear.
2. An optimal solution to (OPT) exists.
3. If `r_k > r_ℓ` for `ℓ > k`, then for any optimal solution, with `k̂ = max {k | p⋆_k > 0}`, we have
   `b_ℓ p⋆_ℓ = z⋆_ℓ` for `ℓ < k̂`.

**Formalization Note.** `b_ℓ` is real for `ℓ < k̂ ≤ K`, so `toReal` is faithful in clause 3. The
linearity of `objective` is a matter of its definition and is not restated. -/
theorem lemma_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r) :
    (ConcaveOn ℝ (Set.Icc 0 1) (g μ 𝒯) ∧
      Convex ℝ {x : (ℕ → ℝ) × (ℕ → ℝ) | IsFeasible μ 𝒯 K b x.1 x.2}) ∧
    (∃ p z, IsOptimal μ 𝒯 K b r p z) ∧
    ((∀ k ∈ Finset.Icc 1 K, ∀ ℓ ∈ Finset.Icc 1 K, k < ℓ → r ℓ < r k) →
      ∀ p z, IsOptimal μ 𝒯 K b r p z →
        ∀ kHat ∈ Finset.Icc 1 K, 0 < p kHat → (∀ k ∈ Finset.Icc 1 K, 0 < p k → k ≤ kHat) →
          ∀ ℓ ∈ Finset.Icc 1 K, ℓ < kHat → (b ℓ).toReal * p ℓ = z ℓ) := by sorry

end PersuasionNetworks
