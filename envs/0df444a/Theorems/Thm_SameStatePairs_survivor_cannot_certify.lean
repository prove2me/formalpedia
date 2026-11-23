-- Prove2me | Theorems.Thm_SameStatePairs_survivor_cannot_certify
-- name    : SameStatePairs.survivor_cannot_certify
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T21:03:24.575324+00:00
-- url     : https://prove2.me/theorems/9b6cdcfb-1dac-4e29-8348-481cb89439f9
-- title:
--   Proposition 2: limits of the surviving bound
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$ and $\sum_zp(z)=1$, and let $k\ge1$. Observations of state $z$ carry independent nuisances $\nu_1\sim q_1$ and $\nu_2\sim q_2$ on finite sets, with $q_m>0$ and $\sum q_m=1$. Write $\rho$ for the scene-explained fraction $\rho(f)=\operatorname{tr}(C_f^{1/2})/k$, where $C_f=\operatorname{Cov}(\mathbb{E}[f(X)\mid Z])$.
--
--   1. If $\rho(f_1)=\rho(f_2)=1$, the bound of eq. (2) is zero:
--   $$2k\Big(1-\min_{m\in\{1,2\}}\rho(f_m)\Big)=0.$$
--   2. If $d_z-1\ge 2k$, there exist centred, whitened state functions $f,g:Z\to\mathbb{R}^k$ such that, viewed as encoders $f(z,\nu_1)=f(z)$ and $g(z,\nu_2)=g(z)$ of the observations, $\rho(f)=\rho(g)=1$ and
--   $$\mathbb{E}\|f(X_1)-Qg(X_2)\|^2=2k\qquad\text{for every }Q\in O(k),$$
--   where the expectation is over paired observations of one state $z\sim p$.
--
--   So eq. (2) can be zero while the aligned error is maximal, and the bound cannot certify good-view alignment.
--
--   **Formalization Note** $k\ge1$ is added because $\rho$ divides by $k$. A state function is an encoder of observations that ignores the nuisance. $d_z-1\ge2k$ is written $2k+1\le|Z|$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 3, Proposition 2, eq. (2), p. 6; proof in Appendix A.3, p. 12

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem survivor_cannot_certify {Z N₁ N₂ : Type*} [Fintype Z] [Fintype N₁] [Fintype N₂] {k : ℕ}
    (hk : 1 ≤ k) (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (q₁ : N₁ → ℝ) (hq₁ : ∀ ν, 0 < q₁ ν) (hq₁1 : ∑ ν, q₁ ν = 1)
    (q₂ : N₂ → ℝ) (hq₂ : ∀ ν, 0 < q₂ ν) (hq₂1 : ∑ ν, q₂ ν = 1) :
    (∀ (e₁ : Z → N₁ → Fin k → ℝ) (e₂ : Z → N₂ → Fin k → ℝ),
      sceneFraction p q₁ e₁ = 1 → sceneFraction p q₂ e₂ = 1 →
      survivorBound k (sceneFraction p q₁ e₁) (sceneFraction p q₂ e₂) = 0) ∧
    (2 * k + 1 ≤ Fintype.card Z →
      ∃ f g : Z → Fin k → ℝ, IsCentered p f ∧ IsWhitened p f ∧ IsCentered p g ∧ IsWhitened p g ∧
        sceneFraction p q₁ (fun z _ => f z) = 1 ∧ sceneFraction p q₂ (fun z _ => g z) = 1 ∧
        ∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
          pairedResidual p q₁ q₂ (fun z _ => f z) (fun z _ => g z) Q = 2 * k) := by sorry

end SameStatePairs
