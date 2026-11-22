-- Prove2me | Theorems.Thm_RestrictedAP_Counting_claim_5_22_uniform
-- name    : RestrictedAP.Counting.claim_5_22_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:29.556814+00:00
-- url     : https://prove2.me/theorems/59024691-9b50-41d8-a109-e08bd5a9085b
-- title:
--   Uniform low-influence counting after truncation
-- statement:
--   This is a uniform quantitative form of Claim 5.22 for low-degree, low-influence functions.
--
--   For every $m$, atom lower bound $s>0$, density $\delta>0$, degree bound $D$, and norm bound $C>0$, there are $\tau,\xi,c>0$ such that the following holds. Let $\Sigma$ be a nonempty alphabet with $|\Sigma|\le m$, and let $\mu$ be a distribution on $\Sigma^3$ having common marginal $\nu$, diagonal support, no $(\mathbb Z,+)$-embedding, and all atoms of probability at least $s$. If $g:\Sigma^n\to\mathbb C$ has Fourier degree at most $D$, satisfies $\|g\|_{L^2(\nu^{\otimes n})}\le C$, has every coordinate influence at most $\tau$, and satisfies
--   $$\operatorname{Re}\mathbb E_{\nu^{\otimes n}}g\ge\delta,
--    \qquad
--    \mathbb E_{\nu^{\otimes n}}|\operatorname{trunc}_{[0,1]}(g)-g|^2\le\xi,$$
--   then
--   $$c\le\mathbb E_{(x,y,z)\sim\mu^{\otimes n}}
--    [\operatorname{trunc}_{[0,1]}g(x)\operatorname{trunc}_{[0,1]}g(y)
--     \operatorname{trunc}_{[0,1]}g(z)].$$
--
--   The thresholds $\tau,\xi$ and the lower bound $c$ depend only on $m,s,\delta,D,C$, not on $n$, $\mu$, or $g$. This uniformity is essential: Proposition 5.28 supplies the positive covariance gap needed by Gaussian reverse hypercontractivity, and its gap must be chosen uniformly among all distributions covered by the atom and alphabet bounds.
--
--   Diagonal support makes all three marginals fully supported, as required by Proposition 5.28. The statement also permits $n=0$, where the function spaces are one-point spaces and no coordinate-influence condition arises.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://arxiv.org/abs/2608.17365, pp. 43–47, Claim 5.22 and Claims 5.23–5.26, using Theorem 5.9 (p. 30), Theorem 5.11 (p. 31), and Proposition 5.28 (pp. 48–49); uniform-in-distribution formulation needed for Lemma 5.27

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_LowInfluence

namespace RestrictedAP.Counting

/-- Uniform form of Claim 5.22: a bounded-degree, bounded-norm, sufficiently low-influence
function with nonnegligible mean and small truncation error has nonnegligible truncated
triple correlation. -/
theorem claim_5_22_uniform (m : ℕ) (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (D : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ τ ξ c : ℝ, 0 < τ ∧ 0 < ξ ∧ 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] [Nonempty Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
      ∀ (n : ℕ) (g : (Fin n → Sig) → ℂ),
        HasDegreeBound ν D g → l2Norm (tensorPow ν n) g ≤ C →
        (∀ i, influence ν i g ≤ τ) →
        δ ≤ (expectC (tensorPow ν n) g).re → truncatedError ν g ≤ ξ →
        c ≤ tripleTrunc μ g := by sorry
