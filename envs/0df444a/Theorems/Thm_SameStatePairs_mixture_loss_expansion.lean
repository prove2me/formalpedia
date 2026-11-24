-- Prove2me | Theorems.Thm_SameStatePairs_mixture_loss_expansion
-- name    : SameStatePairs.mixture_loss_expansion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T21:04:01.11054+00:00
-- url     : https://prove2.me/theorems/b9ad084e-33f3-4f2f-af7b-c18a9d36e28d
-- title:
--   Equation (3): expansion of the mixture loss
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$ and $\sum_zp(z)=1$, let $X$ be a finite observation space with channel $P_{X\mid Z}$ and observation law $P_X(x)>0$, and let $0\le\varepsilon\le1$. Let $P_+^\varepsilon=\varepsilon P_s+(1-\varepsilon)P_X\otimes P_X$, where $P_s$ is the same-state pair law, and let $T_s=AA^*$. For every encoder $f:X\to\mathbb{R}^k$ that is centred and whitened under $P_X$,
--
--   $$L_\varepsilon(f)=\mathbb{E}_{(X,X')\sim P_+^\varepsilon}\|f(X)-f(X')\|^2=2k-2\varepsilon\sum_{j=1}^k\langle f_j,T_sf_j\rangle_{L^2(P_X)}.$$
--
--   This identity turns the loss into a trace against $T_s$, the starting point of Theorem 1.
--
--   **Formalization Note** The world and the observation space are finite, and every observation has positive probability, so $L^2(P_X)$ is the space of all functions on $X$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 4.1, eq. (3), p. 6; derived in Appendix A.1, eq. (5), p. 11

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem mixture_loss_expansion {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq X] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (κ : Z → X → ℝ) (hκ : IsChannel κ) (hX : ∀ x, 0 < obsLaw p κ x)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (f : X → Fin k → ℝ) (hfc : IsCentered (obsLaw p κ) f) (hfw : IsWhitened (obsLaw p κ) f) :
    pairLoss (mixPairLaw p κ ε) f = 2 * k - 2 * ε * topQuad p κ f := by sorry

end SameStatePairs
