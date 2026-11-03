-- Prove2me | Theorems.Thm_StationaryBwK_ratio_minimization
-- name    : StationaryBwK.ratio_minimization
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:50:35.742824+00:00
-- url     : https://prove2.me/theorems/71691f9c-1761-4003-9e4e-dd230f0cae23
-- title:
--   Proof of Theorem 5.2, p.18: $\min_x\max\{\rho,\sigma_c x\}(1+\sigma_r\frac{1-x}{x})=\rho+\sigma_r(\sigma_c-\rho)^+$
-- statement:
--   Let $\rho\in(0,1]$, $\sigma_r,\sigma_c\in[0,1]$, and $f(x)=\max\{\rho,\sigma_c x\}\big(1+\sigma_r\frac{1-x}{x}\big)$ for $x\in(0,1]$. Then:
--
--   1. $f(x)=\max\big\{\rho+\rho\sigma_r\frac{1-x}{x},\ \sigma_r\sigma_c+\sigma_c x(1-\sigma_r)\big\}$ for every $x\in(0,1]$;
--   2. if $\sigma_c>0$, $f$ is non-increasing on $(0,\min\{1,\rho/\sigma_c\}]$ and non-decreasing on $[\rho/\sigma_c,1]$;
--   3. if $\rho\le\sigma_c$, then $f(\rho/\sigma_c)=\rho+\sigma_r(\sigma_c-\rho)$;
--   4. for every $x\in(0,1]$,
--   $$f(x)\ \ge\ \rho+\sigma_r(\sigma_c-\rho)^+ .$$
--
--   The guaranteed fraction of $\mathrm{OPT}_{FD}$ is $f(x)$ for the unknown $x=T^*/T$; its worst case over $x$ is the competitive ratio of Theorem 5.2.
--
--   Differences from the source:
--   - reading: 'The above term is decreasing in x while x ≤ ρ/σc and increasing afterwards. This means that the minimizing x is ρ/σc, which proves the desired competitive ratio'; 'The theorem trivially holds if σc ≤ ρ' → clauses 2–4: monotonicity on (0, min{1, ρ/σc}] and [ρ/σc, 1] for σc > 0, the value f(ρ/σc) = ρ + σr(σc − ρ) when ρ ≤ σc, and the lower bound f ≥ ρ + σr(σc − ρ)⁺ on (0, 1]; reason: this is what the sentences assert on the domain x = T*/T ∈ (0, 1]; when σc < ρ the minimizer is x = 1, the 'trivial' case, and clause 4 covers it
--   - reading: decreasing / increasing → AntitoneOn / MonotoneOn (non-strict); reason: f is constant in x when σr = 0 or σr = 1 on the respective pieces, so strict monotonicity is false there; the minimization only needs the non-strict form
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Theorem 5.2, p.18, last display and the two sentences after it

import Mathlib

namespace StationaryBwK

/-- **The worst case over `x`** (Fikioris & Tardos, arXiv:2302.14686v2, proof of Theorem 5.2,
p.18, last display and the sentence after it). For `ρ ∈ (0, 1]`, `σr, σc ∈ [0, 1]` and
`f(x) = max{ρ, σc x} (1 + σr (1 − x)/x)` on `x ∈ (0, 1]`:
1. `f(x) = max{ρ + ρσr (1 − x)/x, σrσc + σc x (1 − σr)}`;
2. if `σc > 0`, `f` is decreasing while `x ≤ ρ/σc` and increasing afterwards;
3. if `ρ ≤ σc`, the minimizing value is `f(ρ/σc) = ρ + σr(σc − ρ)`;
4. `f(x) ≥ ρ + σr (σc − ρ)⁺` for every `x ∈ (0, 1]` (the competitive ratio of Theorem 5.2; the
   case `σc ≤ ρ` is the one the proof calls trivial).

**Formalization Note.** "Decreasing"/"increasing" are `AntitoneOn`/`MonotoneOn` (non-strict),
on `(0, min{1, ρ/σc}]` and `[ρ/σc, 1]`. `(σc − ρ)⁺` is `max (σc − ρ) 0`. -/
theorem ratio_minimization (ρ σr σc : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hσr₀ : 0 ≤ σr)
    (hσr₁ : σr ≤ 1) (hσc₀ : 0 ≤ σc) (hσc₁ : σc ≤ 1) :
    (∀ x ∈ Set.Ioc (0 : ℝ) 1,
      max ρ (σc * x) * (1 + σr * (1 - x) / x) =
        max (ρ + ρ * σr * (1 - x) / x) (σr * σc + σc * x * (1 - σr))) ∧
    (0 < σc →
      AntitoneOn (fun x : ℝ => max ρ (σc * x) * (1 + σr * (1 - x) / x))
          (Set.Ioc 0 (min 1 (ρ / σc))) ∧
        MonotoneOn (fun x : ℝ => max ρ (σc * x) * (1 + σr * (1 - x) / x))
          (Set.Icc (ρ / σc) 1)) ∧
    (ρ ≤ σc →
      max ρ (σc * (ρ / σc)) * (1 + σr * (1 - ρ / σc) / (ρ / σc)) = ρ + σr * (σc - ρ)) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) 1,
      ρ + σr * max (σc - ρ) 0 ≤ max ρ (σc * x) * (1 + σr * (1 - x) / x)) := by sorry

end StationaryBwK
