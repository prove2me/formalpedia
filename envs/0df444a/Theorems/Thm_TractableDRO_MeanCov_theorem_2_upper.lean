-- Prove2me | Theorems.Thm_TractableDRO_MeanCov_theorem_2_upper
-- name    : TractableDRO.MeanCov.theorem_2_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:33.861228+00:00
-- url     : https://prove2.me/theorems/58ab52fa-4d03-4d2c-af2b-4cab036370e0
-- title:
--   Theorem 2, p. 910 (upper-bound part) — sup over 𝔽₂ of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π²(r⁰, r)
-- statement:
--   Let $F \in \mathbb R^{N\times n}$, $\Sigma \in \mathbb R^{N \times N}$, $\hat{\mathcal V} \subseteq \mathbb R^{n}$, $r^0 \in \mathbb R$ and $r \in \mathbb R^{n}$. Let $\mathbb F_2$ be the family of probability distributions $\mathbb P$ of a random vector $\tilde\zeta \in \mathbb R^{n}$ with finite second moments, mean $\hat\zeta = E_{\mathbb P}(\tilde\zeta) \in \hat{\mathcal V}$ and $E_{\mathbb P}(F(\tilde\zeta - \hat\zeta)(\tilde\zeta - \hat\zeta)'F') = \Sigma$. Then
--
--   $$\sup_{\mathbb P \in \mathbb F_2} E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) \le \pi^2(r^0, r) = \inf_{y:\, F'y = r} \ \sup_{\hat\zeta \in \hat{\mathcal V}} \Big\{ \tfrac12 (r^0 + r'\hat\zeta) + \tfrac12 \sqrt{(r^0 + r'\hat\zeta)^2 + y'\Sigma y} \Big\}.$$
--
--   Both sides are extended reals: the left side is $-\infty$ when $\mathbb F_2$ is empty and the right side is $+\infty$ when $F'y = r$ has no solution.
--
--   This is the bound half of Theorem 2 of Goh and Sim: the deterministic problem $\pi^2$ is a valid, tractable upper bound on the worst-case expected positive part over all distributions with the prescribed mean set and covariance.
--
--   **Formalization Note** No hypothesis on $F$, $\Sigma$ or $\hat{\mathcal V}$ is needed for this half: membership in $\mathbb F_2$ already forces $\Sigma = F\,\mathrm{Cov}_{\mathbb P}(\tilde\zeta)\,F'$, which is positive semidefinite. Objects are those of `TractableDRO.MeanCov.Model`.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Theorem 2 and (22)

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem theorem_2_upper {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (family2 F Sig Vhat) r0 r ≤ pi2 F Sig Vhat r0 r := by sorry

end TractableDRO.MeanCov
