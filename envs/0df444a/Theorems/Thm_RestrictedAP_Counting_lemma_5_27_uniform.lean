-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_5_27_uniform
-- name    : RestrictedAP.Counting.lemma_5_27_uniform
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:07:21.353633+00:00
-- url     : https://prove2.me/theorems/9554cccd-04e8-4b9a-91c1-29b1dcbbdc72
-- title:
--   Lemma 5.27, uniform form — resilient sets have many diagonal-support triples, uniformly over distributions with atoms at least s
-- statement:
--   For $m \in \mathbb N$ and reals $s, \delta > 0$ there are $B_0 \in \mathbb N$ and $c > 0$ with the following property. Let $\Sigma$ be an alphabet with $|\Sigma| \le m$, and let $\mu$ be a distribution on $\Sigma^3$ such that:
--
--   - all three marginals of $\mu$ equal $\nu$;
--   - $\mu(x,x,x) > 0$ for every $x \in \Sigma$;
--   - the support of $\mu$ has no $(\mathbb Z,+)$-embedding;
--   - every atom of $\mu$ has probability at least $s$.
--
--   Let $n, B \in \mathbb N$ with $B \ge B_0$, and let $f : \Sigma^n \to \{0,1\}$ be $(B, 1/2)$-resilient (`Resilient ν B (1/2) f`) with $\mathbb E_{\nu^{\otimes n}} f \ge \delta$. Then
--   $$\Delta_1(f) = \mathbb E_{(x,y,z) \sim \mu^{\otimes n}}[f(x) f(y) f(z)] \ge s^{B+1} c.$$
--
--   The paper's Lemma 5.27 (p. 47) reads: "Suppose $f : \Sigma^n \to \{0,1\}$ is a $(B, 1/2)$ resilient function for $B \gg \Omega_{\rho_1}(1)$, then $\Delta_1(f) \geqslant \alpha^{B+1}\,\Omega_{\rho_0}(\delta^{\Omega_{m,\alpha}(1)})$", where $\alpha$ is the minimum atom probability of $\mu$. The mission states it as `RestrictedAP.Counting.lemma_5_27` with $\alpha$ the exact minimum atom (`IsMinAtom μ α`). This form asks for constants that depend only on a lower bound $s$ for the atoms, not on $\mu$. Theorem 1.4 needs this uniformity, because its $\beta$ depends only on $m$, the atom bound and the density. With $s = \alpha$ this statement gives `lemma_5_27` directly.
--
--   The proof of Theorem 1.4 (p. 48) combines this with Claim 5.14 (`RestrictedAP.Counting.claim_5_14_monotone`), and `RestrictedAP.Counting.theorem_1_4` is submitted as a reduction to the two.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1020.pdf, p. 47, Lemma 5.27, with the constants uniform over all distributions whose atoms are at least s (as the proof of Theorem 1.4, p. 48, uses it)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

namespace RestrictedAP.Counting

theorem lemma_5_27_uniform (m : ℕ) (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
      ∀ (n B : ℕ), B₀ ≤ B →
      ∀ f : (Fin n → Sig) → ℝ, (∀ x, f x = 0 ∨ f x = 1) → Resilient ν B (1 / 2) f →
        δ ≤ expect (tensorPow ν n) f →
        s ^ (B + 1) * c ≤ Delta1 μ f := by sorry

end RestrictedAP.Counting
