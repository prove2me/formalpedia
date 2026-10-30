-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nuclear_norm_ls_frobenius_oracle_bound
-- name    : WainwrightHDS.NucNorm.nuclear_norm_ls_frobenius_oracle_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:49.586987+00:00
-- url     : https://prove2.me/theorems/83605de2-6526-45ea-9387-f93c98ede930
-- title:
--   Proposition 10.6 — Frobenius oracle inequality for nuclear-norm regularized least squares
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^{d_1\times d_2}$ be design matrices with observation operator $[\mathfrak X_n(\Theta)]_i=\langle\!\langle X_i,\Theta\rangle\!\rangle$, let $\Theta^*\in\mathbb R^{d_1\times d_2}$ be arbitrary, and let the responses be $y=\mathfrak X_n(\Theta^*)+w$ for a noise vector $w\in\mathbb R^n$. Write $d'=\min\{d_1,d_2\}$ and $\sigma_1(\Theta^*)\ge\dots\ge\sigma_{d'}(\Theta^*)$ for the singular values of $\Theta^*$. Suppose:
--
--   1. (restricted strong convexity (10.17)) for constants $\kappa>0$ and $c_0>0$,
--   $$\frac{\|\mathfrak X_n(\Delta)\|_2^2}{2n}\;\ge\;\frac{\kappa}{2}|||\Delta|||_F^2 - c_0\,\frac{d_1+d_2}{n}\,|||\Delta|||_{\mathrm{nuc}}^2\qquad\text{for all }\Delta\in\mathbb R^{d_1\times d_2};$$
--   2. (the event $\mathbb G(\lambda_n)$) $\lambda_n>0$ and $\big|\big|\big|\tfrac1n\sum_{i=1}^n w_iX_i\big|\big|\big|_2\le \lambda_n/2$;
--   3. $\widehat\Theta$ is any optimal solution of the nuclear-norm regularized least-squares program (10.16),
--   $$\widehat\Theta\in\arg\min_{\Theta\in\mathbb R^{d_1\times d_2}}\Big\{\frac1{2n}\|y-\mathfrak X_n(\Theta)\|_2^2+\lambda_n|||\Theta|||_{\mathrm{nuc}}\Big\}.$$
--
--   Then for every $r\in\{1,\dots,d'\}$ with $r\le \dfrac{\kappa n}{128\,c_0(d_1+d_2)}$,
--
--   $$
--   |||\widehat\Theta-\Theta^*|||_F^2 \;\le\; \frac92\,\frac{\lambda_n^2}{\kappa^2}\,r \;+\; \frac1\kappa\Big\{2\lambda_n\sum_{j=r+1}^{d'}\sigma_j(\Theta^*) + \frac{32\,c_0(d_1+d_2)}{n}\Big[\sum_{j=r+1}^{d'}\sigma_j(\Theta^*)\Big]^2\Big\}.
--   $$
--
--   This oracle inequality splits the error into an estimation term, proportional to the target rank $r$, and an approximation term governed by the tail singular values of $\Theta^*$; it holds for every $\Theta^*$, not only low-rank ones, and $r$ may be chosen to minimize the right-hand side. For $\Theta^*$ of rank $r$ the tail vanishes and the bound becomes $\tfrac92\,r\lambda_n^2/\kappa^2$ (10.19).
--
--   **Formalization Note** The statement is deterministic: conditioning on $\mathbb G(\lambda_n)$ is the hypothesis on $w$. There is no hypothesis $n\ge1$: with $n=0$ Lean's division gives $x/0=0$, and the restricted strong convexity hypothesis then fails for every $\Delta\ne0$ (which exists because $1\le r\le d'$), so the case is excluded by the other hypotheses.
--
--   Differences from the source:
--   - reading: "conditioned on the event G(λ_n) = {|||(1/n)Σ w_i X_i|||₂ ≤ λ_n/2}" → deterministic hypothesis opNorm2 ((1/n)•Σ w_i•X_i) ≤ λ/2 on the vector w; reason: the proposition is a corollary of Theorem 9.19, which the book calls a deterministic result (p. 280); no probability law of w is involved
--   - reading: c₀ "another universal constant of secondary importance" → an arbitrary real c₀ > 0 (a binder); reason: the stronger reading — the claim for every c₀ > 0 covers whatever value the universal constant has
--   - encoding: r ≤ κn/(128c₀(d₁+d₂)) → 128·c₀·(d₁+d₂)·r ≤ κ·n in ℝ; reason: multiplied out by the positive number 128c₀(d₁+d₂) (c₀ > 0 and d₁ + d₂ ≥ 2 once r ≥ 1 exists); same instances
--   - encoding: σ_j(Θ*), j = r+1, …, d' (1-based, sorted) → singVal j Θstar, j ∈ [r, min d₁ d₂) (0-based, Mathlib's sorted singularValues); reason: Lean convention; same instances
--   - encoding: Θ̂ ∈ arg min of (10.16) → hypothesis ∀ Θ, lsNucObjective X y λ Θ̂ ≤ lsNucObjective X y λ Θ; reason: "any optimal solution" is any global minimizer; no existence or uniqueness is claimed
--   - encoding: n ≥ 1 implicit → no binder; reason: at n = 0 Lean's x/0 = 0 makes the restricted strong convexity hypothesis false for every Δ ≠ 0, so n = 0 is excluded by the other hypotheses
--   - encoding: indices i = 1..n, j₁ = 1..d₁, j₂ = 1..d₂ → Fin n, Fin d₁, Fin d₂ (0-based); λ_n → lam; reason: Lean convention; same instances
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.2, p. 319 (PDF p. 339), Proposition 10.6, Eq. (10.18); program (10.16) and condition (10.17), p. 319 (PDF p. 339); model (10.2)–(10.3), p. 312 (PDF p. 332)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective

namespace WainwrightHDS.NucNorm

/-- **Proposition 10.6 — Frobenius oracle inequality for nuclear-norm regularized least squares.**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.2, p. 319 (PDF p. 339), Proposition 10.6, Eq. (10.18), with (10.16) and (10.17).

Observations `y = 𝔛_n(Θ*) + w` (10.3). Suppose `𝔛_n` satisfies restricted strong convexity
(10.17) with curvature `κ > 0` and constant `c₀ > 0`:
`‖𝔛_n(Δ)‖₂²/(2n) ≥ (κ/2)|||Δ|||_F² − c₀((d₁+d₂)/n)|||Δ|||_nuc²` for all `Δ`. On the event
`|||(1/n) Σ_i w_i X_i|||₂ ≤ λ_n/2`, every minimizer `Θ̂` of (10.16) with `λ_n > 0` satisfies, for every
`r ∈ {1, …, d'}` with `r ≤ κn/(128 c₀(d₁+d₂))`,
`|||Θ̂ − Θ*|||_F² ≤ (9/2)(λ_n²/κ²) r + (1/κ){2λ_n Σ_{j=r+1}^{d'} σ_j(Θ*) + (32c₀(d₁+d₂)/n)[Σ_{j=r+1}^{d'} σ_j(Θ*)]²}`.

Formalization Note: deterministic ("conditioned on the event" = hypothesis `hG` on `w`). `c₀` is
any positive real. The range of `r` is multiplied out: `128 c₀ (d₁+d₂) r ≤ κ n`. The tail
`Σ_{j=r+1}^{d'} σ_j(Θ*)` is `Σ_{j ∈ [r, min d₁ d₂)} singVal j Θ*` (0-based, sorted singular
values). No `0 < n` binder: for `n = 0` Lean reads `x / 0 = 0`, and then `hRSC` fails at any
`Δ ≠ 0` (and `1 ≤ r ≤ min d₁ d₂` gives such a `Δ`), so the hypotheses already exclude `n = 0`.
`λ_n` is `lam`. -/
theorem nuclear_norm_ls_frobenius_oracle_bound {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n) :
    frobSq (Θhat - Θstar) ≤
      9 / 2 * (lam ^ 2 / κ ^ 2) * r +
        1 / κ * (2 * lam * ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar +
          32 * c₀ * ((d₁ : ℝ) + d₂) / n *
            (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2) := by sorry

end WainwrightHDS.NucNorm
