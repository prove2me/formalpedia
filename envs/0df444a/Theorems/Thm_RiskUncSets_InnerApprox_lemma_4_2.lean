-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_lemma_4_2
-- name    : RiskUncSets.InnerApprox.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:06:43.314645+00:00
-- url     : https://prove2.me/theorems/84cbfe33-194b-4ec0-9730-c18c2d395adf
-- title:
--   Lemma 4.2, p. 1493 — for q̃ = λq + (1 − λ)e_N and λ ≠ 0, ‖a − â‖_{q̃,𝒜} = (1/|λ|)‖a − â‖_{q,𝒜}
-- statement:
--   Let $N \ge 1$, let $q \in \hat\Delta^N_{\mathrm{sym}}$ be a centrally symmetric generator, let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$ have sample mean $\hat a$, and let $\lambda \in \mathbb R$ with $\lambda \ne 0$. Then the vector $\tilde q = \lambda q + (1-\lambda) e_N$ satisfies
--   $$\|a - \hat a\|_{\tilde q,\mathcal A} = \frac{1}{|\lambda|}\,\|a - \hat a\|_{q,\mathcal A}\qquad\text{for all } a \in \mathbb R^n,$$
--   where $\|\cdot\|_{q,\mathcal A}$ is the Minkowski functional (12) of $\tilde\pi_q(\mathcal A) = \Pi_q(\mathcal A) - \hat a$.
--
--   So, in the norm of a fixed centrally symmetric generator, mixing with $e_N$ shrinks or enlarges the unit ball by exactly the factor $|\lambda|$; maximizing $\lambda$ therefore maximizes the inner approximation in Theorem 4.5.
--
--   **Formalization Note** The statement is written for $w = a - \hat a$ ranging over $\mathbb R^n$. Two corrections to the printed (13) are made and disclosed: the right-hand side uses $q$, not $\tilde q$ (the page prints $\tilde q$ on both sides, which would make the identity false for $|\lambda| \ne 1$), and $\lambda \ne 0$ is assumed because the right-hand side contains $1/|\lambda|$. When $\Pi_q(\mathcal A)$ has empty interior the page's two sides are both $+\infty$ off $\hat a$; with Mathlib's `gauge` both are the junk value $0$ there, so the identity remains consistent.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1493, Lemma 4.2, (13)

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Lemma 4.2, (13): `‖a − â‖_{q̃,𝒜} = (1/|λ|) ‖a − â‖_{q,𝒜}` for `q̃ = λq + (1−λ)e_N`,
`q ∈ Δ̂ᴺ_sym`, `λ ≠ 0`. -/
theorem lemma_4_2 {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (lam : ℝ) (hlam : lam ≠ 0) :
    ∀ w : Fin n → ℝ, normQ (mix q lam) a w = (1 / |lam|) * normQ q a w := by sorry

end RiskUncSets.InnerApprox
