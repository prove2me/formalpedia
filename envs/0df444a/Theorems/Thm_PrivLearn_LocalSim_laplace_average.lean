-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_laplace_average
-- name    : PrivLearn.LocalSim.laplace_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:12.000309+00:00
-- url     : https://prove2.me/theorems/e6e081f7-b08f-42ca-861c-84dfedc103ea
-- title:
--   Proof of Lemma 5.6, p. 20 — the average of n i.i.d. Lap(2b/ε) noises lies in [−τ/2, τ/2] with probability ≥ 1 − β/2
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $b,\varepsilon,\tau>0$ with $\varepsilon\tau\le 4b$, let $0<\beta\le 1/2$, and let $\eta_1,\dots,\eta_n$ be i.i.d. $\mathrm{Lap}(2b/\varepsilon)$ with
--   $$n\ \ge\ c\cdot\frac{\ln(1/\beta)\,b^2}{\varepsilon^2\tau^2}.$$
--   Then
--   $$\Pr\Bigl[\Bigl|\frac1n\sum_{i=1}^n\eta_i\Bigr|>\frac\tau2\Bigr]\le\frac\beta2.$$
--
--   This bounds the effect of the Laplace noise in $\mathcal A_g$; the paper obtains it from a tail bound for sums of Laplace variables (Lemma A.3) with $\lambda=2b/\varepsilon$.
--
--   **Formalization Note.** The paper writes "$O(\ln(1/\beta)b^2/(\varepsilon^2\tau^2))$ samples are sufficient"; we state an absolute constant $c$, chosen before all other quantities. Two hypotheses are added because the claim is false without them. (i) $\varepsilon\tau\le4b$, i.e. $\tau/2\le\lambda$: the sub-Gaussian tail used for Laplace averages only holds for deviations up to the order of the scale; for $\varepsilon\tau/b$ large, $n=1$ is allowed and $\Pr[|\eta_1|>\tau/2]=e^{-\varepsilon\tau/(4b)}$ exceeds $\beta/2$ for $\beta=e^{-(\varepsilon\tau/b)^2/c}$. (ii) $\beta\le1/2$: for $\beta$ close to $1$ the threshold allows $n=1$ with $\varepsilon\tau/b$ small, and then the probability is close to $1>\beta/2$. Lemma A.3 itself (an equality, false as printed) is not posed.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 20, proof of Lemma 5.6, second paragraph (via Lemma A.3, p. 35)

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy

namespace PrivLearn.LocalSim

open MeasureTheory

/-- Proof of Lemma 5.6 (p. 20), Laplace step: there is an absolute constant `c > 0` such that if
`η_1, …, η_n` are i.i.d. `Lap(2b/ε)` and `n ≥ c · ln(1/β) b² / (ε² τ²)`, then the average of the
`η_i` lies outside `[−τ/2, τ/2]` with probability at most `β/2`. Stated in the regime
`ε τ ≤ 4 b` (i.e. `τ/2 ≤ λ = 2b/ε`) and for `β ≤ 1/2`, without which it is false. -/
theorem laplace_average :
    ∃ c : ℝ, 0 < c ∧
      ∀ (b ε τ β : ℝ) (n : ℕ), 0 < b → 0 < ε → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β ≤ 1 / 2 →
        c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
        (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε))
            {η | τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i|}
          ≤ ENNReal.ofReal (β / 2) := by sorry

end PrivLearn.LocalSim
