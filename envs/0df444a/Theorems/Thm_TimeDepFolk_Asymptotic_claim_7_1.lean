-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_claim_7_1
-- name    : TimeDepFolk.Asymptotic.claim_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:16.225813+00:00
-- url     : https://prove2.me/theorems/40b3feaf-3cc3-4253-a0e3-17a3c3279f61
-- title:
--   Claim 7.1, p. 33 — perturbing one vertex by η′ moves the barycentric coefficients by at most η′ L R_φ
-- statement:
--   Let $x_1,\dots,x_L\in\mathbb R^I$ with $L\le |I|+1$, such that for every $\ell$ the vectors $\{x_s-x_\ell: s\ne\ell\}$ are linearly independent. Let $x=\sum_\ell\lambda_\ell x_\ell$ be a convex combination, let $\eta>0$ with $B_\eta(x)\subseteq\operatorname{co}\{x_\ell\}$, where $B_\eta(z)=\{y:\|y-z\|_\infty\le\eta\}$, and put $\eta'=\eta/5$. For each $\ell$ let $X_\ell=(x_s-x_\ell)_{s\ne\ell}$ be the $I\times(L-1)$ matrix and $R_\ell=\|X_\ell^T\|_\infty\|(X_\ell X_\ell^T)^{-1}\|_\infty$, with $\|\cdot\|_\infty$ the maximum-row-sum norm.
--
--   Fix an index $\varphi$ and a point $x'_\varphi\in B_{\eta'}(x_\varphi)$. If $x$ is also expressed by the convex combination $x=\lambda'_\varphi x'_\varphi+\sum_{\ell\ne\varphi}\lambda'_\ell x_\ell$, then
--   $$|\lambda'_\ell-\lambda_\ell|\le\eta' L R_\varphi\qquad\text{for all }\ell\in\{1,\dots,L\}.$$
--
--   This sensitivity bound is the step of the proof of Lemma 4.4 that allows a vertex of the decomposition to be replaced by a nearby point while keeping every coefficient under control.
--
--   **Formalization Note.** The paper's $\varphi(1)$ is a fixed index `φ : Fin L`, and $x'_{\varphi(1)}$ is any point of $B_{\eta'}(x_{\varphi(1)})$ (the page sets it to $x_{\varphi(1),1}$). Linear independence of the edge vectors at every vertex is `AffineIndependent ℝ x`. The ball hypothesis forces $L=|I|+1$, which makes $X_\varphi X_\varphi^T$ invertible, so Mathlib's matrix inverse in `Rcoef` is the true inverse. The page's "w.l.o.g. each $\lambda_\ell>0$" is not used by the claim and is not assumed. The sup norm on `ι → ℝ` is $\|\cdot\|_\infty$.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 33, §7.1, Claim 7.1 and its setup (X_ℓ, R_ℓ, η′ = η/5)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem claim_7_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (hL : L ≤ Fintype.card ι + 1) (x : Fin L → ι → ℝ) (hx : AffineIndependent ℝ x)
    (lam : Fin L → ℝ) (hlam0 : ∀ ℓ, 0 ≤ lam ℓ) (hlam1 : ∑ ℓ, lam ℓ = 1)
    (x0 : ι → ℝ) (hx0 : ∑ ℓ, lam ℓ • x ℓ = x0)
    (η : ℝ) (hη : 0 < η) (hball : Metric.closedBall x0 η ⊆ convexHull ℝ (Set.range x))
    (φ : Fin L) (x' : ι → ℝ) (hx' : x' ∈ Metric.closedBall (x φ) (η / 5))
    (lam' : Fin L → ℝ) (hlam'0 : ∀ ℓ, 0 ≤ lam' ℓ) (hlam'1 : ∑ ℓ, lam' ℓ = 1)
    (hx0' : lam' φ • x' + ∑ ℓ ∈ Finset.univ.erase φ, lam' ℓ • x ℓ = x0) :
    ∀ ℓ, |lam' ℓ - lam ℓ| ≤ η / 5 * L * Rcoef x φ := by sorry

end TimeDepFolk.Asymptotic
