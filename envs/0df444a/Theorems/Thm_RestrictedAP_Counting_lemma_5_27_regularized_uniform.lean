-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_5_27_regularized_uniform
-- name    : RestrictedAP.Counting.lemma_5_27_regularized_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:06.086646+00:00
-- url     : https://prove2.me/theorems/509988c9-11a2-4931-a2a5-7315ef1326a0
-- title:
--   Regularized counting interface for resilient functions, uniform over atom bounds
-- statement:
--   This is the regularization and good-restriction interface in the proof of Lemma 5.27.
--
--   Fix $m$ and $s,\delta>0$. There are a degree bound $D$ and a norm bound $C>0$ such that, for every prescribed influence error $\tau>0$ and truncation error $\xi>0$, there are $B_0$ and $c>0$ with the following property. Let $|\Sigma|\le m$ be nonempty, let $\mu$ be a distribution on $\Sigma^3$ with common marginal $\nu$, diagonal support, no $(\mathbb Z,+)$-embedding, and all atoms of probability at least $s$. If $f:\Sigma^n\to\{0,1\}$ is $(B,1/2)$-resilient for $B\ge B_0$ and $\mathbb E_{\nu^{\otimes n}}f\ge\delta$, then there is $g:\Sigma^n\to\mathbb C$ satisfying:
--
--   1. $g$ has Fourier degree at most $D$ and $\|g\|_{L^2(\nu^{\otimes n})}\le C$;
--   2. every coordinate influence satisfies $I_i[g]\le\tau$;
--   3. $\operatorname{Re}\mathbb E_{\nu^{\otimes n}}g\ge\delta/256$;
--   4. $\mathbb E_{\nu^{\otimes n}}|\operatorname{trunc}_{[0,1]}(g)-g|^2\le\xi$; and
--   5. the original triple correlation is controlled by the truncated one:
--   $$s^{B+1}c\;\mathbb E_{(x,y,z)\sim\mu^{\otimes n}}
--    [\operatorname{trunc}_{[0,1]}g(x)\operatorname{trunc}_{[0,1]}g(y)
--     \operatorname{trunc}_{[0,1]}g(z)]\le\Delta_1(f).$$
--
--   The constants $D,C$ depend only on $m,s,\delta$, while $B_0,c$ may also depend on $\tau,\xi$. The function $g$ packages the decoupled function $\widetilde F_{d,w}(\vec b_\star,\cdot)$ after extending it back to the original coordinate set by ignoring the restricted coordinates. The numerical density denominator $256$ is the one used before the Gaussian argument on p. 45.
--
--   This intermediate statement separates the arithmetic-regularity work in §§5.2.2–5.2.4 from the invariance and Gaussian work in §5.2.5; it is not a separately numbered assertion in the paper.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://arxiv.org/abs/2608.17365, pp. 32–47, proof of Lemma 5.27, especially Claims 5.15, 5.17–5.21 and the final parameter combination on p. 47; intermediate decomposition statement

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience
import Definitions.Def_RestrictedAP_Counting_LowInfluence

namespace RestrictedAP.Counting

/-- The regularization, good-restriction and decoupling part of the proof of Lemma 5.27,
packaged as a bounded-degree low-influence approximation whose truncated triple correlation
still controls `Delta1`. This is an intermediate consequence of pp. 32–47, not an additional
standalone numbered claim in the paper. -/
theorem lemma_5_27_regularized_uniform (m : ℕ) (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ D : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ τ ξ : ℝ, 0 < τ → 0 < ξ → ∃ B₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] [Nonempty Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
      ∀ (n B : ℕ), B₀ ≤ B →
      ∀ f : (Fin n → Sig) → ℝ, (∀ x, f x = 0 ∨ f x = 1) → Resilient ν B (1 / 2) f →
        δ ≤ expect (tensorPow ν n) f →
      ∃ g : (Fin n → Sig) → ℂ,
        HasDegreeBound ν D g ∧ l2Norm (tensorPow ν n) g ≤ C ∧
        (∀ i, influence ν i g ≤ τ) ∧
        δ / 256 ≤ (expectC (tensorPow ν n) g).re ∧ truncatedError ν g ≤ ξ ∧
        s ^ (B + 1) * c * tripleTrunc μ g ≤ Delta1 μ f := by sorry
