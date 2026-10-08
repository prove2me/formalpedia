-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_proposition_4_2
-- name    : RiskUncSets.InnerApprox.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:06:38.334877+00:00
-- url     : https://prove2.me/theorems/1f76b84d-b88d-4f06-b544-95e72ad105c5
-- title:
--   Proposition 4.2, p. 1492 — for q ∈ Δ̂ᴺ_sym the Minkowski functional (12) of the shifted q-permutohull is a norm
-- statement:
--   Let $N \ge 1$, let $q \in \hat\Delta^N_{\mathrm{sym}}$ be a centrally symmetric (comonotone) generator, let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$ have sample mean $\hat a = Ae_N$, and let $\tilde\pi_q(\mathcal A) = \Pi_q(\mathcal A) - \hat a$. Assume that $\Pi_q(\mathcal A)$ has nonempty interior. Then the function
--   $$\|w\|_{q,\mathcal A} = \inf\{\alpha > 0 : w/\alpha \in \tilde\pi_q(\mathcal A)\}$$
--   is a norm on $\mathbb R^n$:
--
--   1. $\|w\|_{q,\mathcal A} = 0$ if and only if $w = 0$;
--   2. $\|\beta w\|_{q,\mathcal A} = |\beta|\,\|w\|_{q,\mathcal A}$ for every $\beta \in \mathbb R$;
--   3. $\|w_1 + w_2\|_{q,\mathcal A} \le \|w_1\|_{q,\mathcal A} + \|w_2\|_{q,\mathcal A}$.
--
--   With $w = a - \hat a$ this is the paper's norm $\|a - \hat a\|_{q,\mathcal A}$ of (12). It is the yardstick in which Theorem 4.5 measures the size of an inner approximation.
--
--   **Formalization Note** The nonempty-interior hypothesis is added: without it (for instance $q = e_N$, or all $a_i$ equal, where $\Pi_q(\mathcal A) = \{\hat a\}$) the infimum (12) is $+\infty$ off $0$ and the function is not a norm; Mathlib's `gauge` would return $0$ there instead. Nonnegativity of $\|\cdot\|_{q,\mathcal A}$ holds for every gauge and is not restated. Interior is taken in the product topology of $\mathbb R^n$, which is the Euclidean one.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1492, Proposition 4.2, (12)

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proposition 4.2: for `q ∈ Δ̂ᴺ_sym` the gauge (12) of `π̃_q(𝒜)` is a norm, provided
`Π_q(𝒜)` has nonempty interior (added: otherwise (12) is `+∞` off `0`). -/
theorem proposition_4_2 {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (hint : (interior (permutohull q a)).Nonempty) :
    (∀ w : Fin n → ℝ, normQ q a w = 0 ↔ w = 0) ∧
    (∀ (β : ℝ) (w : Fin n → ℝ), normQ q a (β • w) = |β| * normQ q a w) ∧
    ∀ w₁ w₂ : Fin n → ℝ, normQ q a (w₁ + w₂) ≤ normQ q a w₁ + normQ q a w₂ := by sorry

end RiskUncSets.InnerApprox
