-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_primal_two_point
-- name    : UniformDRO.LowerBound.primal_two_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:59.187469+00:00
-- url     : https://prove2.me/theorems/db3900a2-a185-4034-8141-e73a6a93f008
-- title:
--   Proof of Lemma 12 (App. D.1.1), p. 47 — R_k(Z) = z₀ + (z₁ − z₀) sup{q ∈ [0,1] : (1−p)^{1−k}(1−q)^k + p^{1−k}q^k ≤ c_k^k}
-- statement:
--   Let $k > 1$, $\rho > 0$ and $c_k = (1 + k(k-1)\rho)^{1/k}$. Let $z_0 \le z_1$, $p \in (0,1)$, and let $Z = z_0$ with probability $1-p$ and $Z = z_1$ with probability $p$. Then
--   $$\mathcal R_k(Z) = z_0 + (z_1 - z_0)\,\sup\Bigl\{ q \in [0,1] \;:\; (1-p)^{1-k}(1-q)^k + p^{1-k} q^k \le c_k^k \Bigr\}.$$
--
--   The supremum runs over the mass $q$ that an alternative distribution places on $z_1$; the constraint is the Cressie–Read divergence condition $D_{f_k}(Q\|P) \le \rho$ for two-point laws, rewritten with $c_k^k = 1 + k(k-1)\rho$. This primal formula is how the proof of Lemma 12 obtains the lower bound of the third claim.
--
--   **Formalization Note.** The page uses the formula for $p \in (0,1)$, where the negative powers $p^{1-k}$ and $(1-p)^{1-k}$ are finite; the statement keeps that range (Lean's `Real.rpow` at base $0$ would give a meaningless value). The set contains $q = p$ and lies in $[0,1]$, so the real supremum is genuine.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Lemma 12 (App. D.1.1), p. 47, first display

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem primal_two_point (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id =
      z₀ + (z₁ - z₀) * sSup {q ∈ Set.Icc (0 : ℝ) 1 |
        (1 - p) ^ (1 - k) * (1 - q) ^ k + p ^ (1 - k) * q ^ k ≤ UniformDRO.Concentration.ck k ρ ^ k} := by sorry

end UniformDRO.LowerBound
