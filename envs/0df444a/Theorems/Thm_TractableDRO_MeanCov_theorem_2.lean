-- Prove2me | Theorems.Thm_TractableDRO_MeanCov_theorem_2
-- name    : TractableDRO.MeanCov.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:32.835016+00:00
-- url     : https://prove2.me/theorems/b7c02672-b37d-45e5-8fef-fcf3613cca9b
-- title:
--   Theorem 2, p. 910 — sup over 𝔽₂ of E_ℙ((r⁰ + r′ζ̃)⁺) = π²(r⁰, r)
-- statement:
--   Let $\tilde\zeta \in \mathbb R^{n}$ be the segregated uncertainty and let $F \in \mathbb R^{N \times n}$ be the full-row-rank matrix relating it to the primitive uncertainty $\tilde z = F\tilde\zeta + g \in \mathbb R^{N}$. Let $\Sigma \in \mathbb R^{N\times N}$ be symmetric positive semidefinite and let $\hat{\mathcal V} \subseteq \mathbb R^{n}$ be nonempty. Let $\mathbb F_2$ be the family of all distributions $\mathbb P$ of $\tilde\zeta$ with finite second moments such that
--
--   $$\mathbb F_2 = \Big\{\mathbb P :\ \hat\zeta = E_{\mathbb P}(\tilde\zeta) \in \hat{\mathcal V},\ E_{\mathbb P}\big(F(\tilde\zeta - \hat\zeta)(\tilde\zeta - \hat\zeta)'F'\big) = \Sigma\Big\}.$$
--
--   Then for every $r^0 \in \mathbb R$ and $r \in \mathbb R^{n}$,
--
--   $$\sup_{\mathbb P \in \mathbb F_2} E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) = \pi^2(r^0, r) = \inf_{y:\, F'y = r} \ \sup_{\hat\zeta \in \hat{\mathcal V}} \Big\{ \tfrac12 (r^0 + r'\hat\zeta) + \tfrac12 \sqrt{(r^0 + r'\hat\zeta)^2 + y'\Sigma y} \Big\},$$
--
--   with both sides in $[-\infty, +\infty]$ and the infimum over an empty set equal to $+\infty$.
--
--   This is Theorem 2 of Goh and Sim: $\pi^2$ is a tight upper bound on the worst-case expected positive part of an affine function of the uncertainty when only a set containing the mean and the covariance of the primitive uncertainties are known. It is the mean–covariance building block of the paper's unified bound (Theorem 4) and of its deflected linear decision rules.
--
--   **Formalization Note** The hypotheses that $\Sigma$ is positive semidefinite, that $F$ has full row rank (p. 906: "F has to be full rank"), and that $\hat{\mathcal V}$ is nonempty are implicit in the paper; each is needed for the equality. The covariance condition is $F\,\mathrm{Cov}_{\mathbb P}(\tilde\zeta)\,F' = \Sigma$, equal to the paper's expectation by linearity. Objects are those of `TractableDRO.MeanCov.Model`, with values in `EReal`.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Theorem 2 and (22); p. 905 (§3); p. 906 ((9), F full rank)

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem theorem_2 {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ))
    (hV : Vhat.Nonempty) (hSig : Sig.PosSemidef) (hF : Function.Surjective F.mulVec)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (family2 F Sig Vhat) r0 r = pi2 F Sig Vhat r0 r := by sorry

end TractableDRO.MeanCov
