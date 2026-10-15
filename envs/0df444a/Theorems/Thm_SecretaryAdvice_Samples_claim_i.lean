-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_claim_i
-- name    : SecretaryAdvice.Samples.claim_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:57.177678+00:00
-- url     : https://prove2.me/theorems/b5d6366a-7717-4a4e-8787-29bb6c83c688
-- title:
--   Proof of Theorem 16, claim (i), p. 16 — the perturbation Δ(i,s) = δ/(s*+1)·∏_{t=1}^{i*−2}(s+t)/(s*+t+1) for i < i*, s ≤ s*
-- statement:
--   Fix $k$, a signal $s^*\in\{0,\dots,k\}$, an index $i^*$ and $\delta\in\mathbb R$, and let $\Delta$ be the perturbation of the proof of Theorem 16: $\Delta(i^*,s^*)=-\delta$, $\Delta(i,s)=0$ for all other $i\ge i^*$, and $\Delta(i,s)=-\sum_{j=i+1}^{i^*}\sum_{s'\ge s}\Delta(j,s')\,c(j,s',i,s)$ for $i<i^*$. Then:
--
--   1. For $i=i^*$: $\Delta(i^*,s^*)=-\delta$ and $\Delta(i^*,s)=0$ for $s\ne s^*$.
--   2. For $1\le i<i^*$ and $s\in\{0,\dots,k\}$:
--   $$\Delta(i,s)=\begin{cases}\delta\cdot\dfrac{1}{s^*+1}\displaystyle\prod_{t=1}^{i^*-2}\frac{s+t}{s^*+t+1}, & s\le s^*,\\[1ex] 0, & s>s^*.\end{cases}$$
--
--   The perturbation lowers $u(i^*,s^*)$ by $\delta$ and compensates in the earlier rounds so that every dual constraint keeps its slack. The closed form shows the compensation is nonnegative when $\delta\ge0$.
--
--   **Formalization Note** $\Delta$ is the definition `delta` of the LP file; it does not depend on the dual solution $u$, only on $(k,i^*,s^*,\delta)$. The product $\prod_{t=1}^{i^*-2}$ is empty (equal to $1$) when $i^*=2$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 16, proof sketch of Theorem 16, claim (i); full proof in Appendix A, pp. 25–26

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_LP
open Finset

namespace SecretaryAdvice.Samples

theorem claim_i (k istar sstar : ℕ) (δ : ℝ) (hsstar : sstar ≤ k) :
    (∀ s : ℕ, delta k istar sstar δ istar s = if s = sstar then -δ else 0) ∧
    ∀ i s : ℕ, 1 ≤ i → i < istar → s ≤ k →
      delta k istar sstar δ i s =
        if s ≤ sstar then
          δ * (1 / ((sstar : ℝ) + 1) *
            ∏ t ∈ Icc 1 (istar - 2), ((s : ℝ) + t) / ((sstar : ℝ) + t + 1))
        else 0 := by sorry

end SecretaryAdvice.Samples
