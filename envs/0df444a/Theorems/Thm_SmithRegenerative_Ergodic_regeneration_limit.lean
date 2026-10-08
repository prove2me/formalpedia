-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_regeneration_limit
-- name    : SmithRegenerative.Ergodic.regeneration_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:23.920989+00:00
-- url     : https://prove2.me/theorems/8757212a-c811-4e8d-a74a-6d48608ee04b
-- title:
--   §5·3, proof of Theorem 7 — w_{t+Z_t}/t → κ₁/μ₁ with probability one
-- statement:
--   Under the hypotheses of Theorem 7 — $w_t$ a cumulative process, $\mu_1 = E t_1 < \infty$, $\tilde\kappa_1 = E\tilde y_1 < \infty$, $t_0 = 0$ and $w_0 = 0$ — let $Z_t = \sum_{i=1}^{n_t+1} t_i - t$. Then, with probability one,
--   $$\lim_{t \to \infty} \frac{w_{t+Z_t}}{t} = \frac{\kappa_1}{\mu_1},$$
--   where $\kappa_1 = E y_1$.
--
--   This is the ergodic theorem along the regeneration epochs $t + Z_t = T_{n_t+1}$; Lemma 8 then transfers it to all times $t$.
--
--   **Formalization Note** $\mu_1 < \infty$ and $\tilde\kappa_1 < \infty$ are integrability hypotheses; $\mu_1 > 0$ follows from $P\{t_1 = 0\} < 1$ and is not assumed separately. The limit is along real $t \to \infty$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 27, §5·3, proof of Theorem 7 (display after (5·3·4))

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **The ergodic limit along regeneration epochs** (Smith, *Regenerative stochastic processes*,
Proc. R. Soc. Lond. A 232(1188):6–31 (1955), §5·3, proof of Theorem 7, p. 27, unnumbered):
"Thus, from (5·3·3) and (5·3·4), lim_{t=∞} w_{t+Z_t}/t = κ₁/μ₁, with probability one."

Hypotheses are those of Theorem 7: `w_t` a cumulative process, `μ₁ < ∞`, `κ̃₁ < ∞`, `t₀ = 0`,
`w₀ = 0`.

Formalization Note: `t + Z_t = Σ_{i=1}^{n_t+1} t_i` is a regeneration epoch. `μ₁ < ∞` is
integrability of `t₁` and `κ̃₁ < ∞` integrability of `ỹ₁`; `μ₁ = ∫ t₁ dP` (strictly positive,
since `P{t₁ = 0} < 1`; not assumed separately) and `κ₁ = ∫ y₁ dP`. `w₀ = 0` holds at every
sample point. `IsCumulativeProcess` reads (C1) literally, with `ỹ_n` identically distributed and
no joint independence of `t` and `y`. The limit is along real `t → ∞`. -/
theorem regeneration_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w (s + Z t s ω) ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic
