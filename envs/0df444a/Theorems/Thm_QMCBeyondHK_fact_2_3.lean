-- Prove2me | Theorems.Thm_QMCBeyondHK_fact_2_3
-- name    : QMCBeyondHK.fact_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:07.951221+00:00
-- url     : https://prove2.me/theorems/57493448-bcba-426f-a54d-ee50f3d9a968
-- title:
--   Fact 2.3 ([DFGGR19]) — the retained point $z_t$ has density $\mu_t$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, and let $(x_t, \xi_t, y_t)_{t\ge 0}$ be an independent uniform input stream on a probability space $(\Omega,\mathbb P)$. Let $(\mu_t)$ be a target-density rule of the $(1+\varepsilon)$-online thinning framework, and let $z_t$ be the point retained at step $t$ ($z_t = x_t$ if $\xi_t \le \mu_t(x_t) - \varepsilon/2$, else $z_t = y_t$). Then for every step $t$ and every Borel set $B \subseteq \mathbb R^d$,
--   $$
--   \mathbb P\big(z_t \in B \,\big|\, \mathcal F_t\big) = \int_{B \cap [0,1)^d} \mu_t(x)\,dx \qquad \text{almost surely,}
--   $$
--   where $\mathcal F_t$ is the $\sigma$-algebra of the randomness of steps $0,\dots,t-1$. That is, conditionally on the past, $z_t$ has density $\mu_t$.
--
--   This is the basic fact about rejection sampling on which every moment computation of the analysis rests.
--
--   Differences from the source:
--   - generalization: a (1 + ε)-online thinning strategy, whose target density is chosen from the points retained so far → any target-density rule determined measurably by the inputs of the earlier steps, with values in [1 − ε/2, 1 + ε/2] on the cube and integral one; reason: every strategy of the paper is such a rule (density_integral_eq_one for Haar-thinning)
--   - encoding: z_t has density µ_t → the conditional law of z_t given the randomness of steps < t has density µ_t: P(z_t ∈ B | F_t) = ∫_{B ∩ [0,1)^d} µ_t a.s. for every Borel B; reason: µ_t is itself random, determined by the earlier steps, so 'has density' is a conditional statement
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Fact 2.3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_QMCBeyondHK_IsThinningDensity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Fact 2.3 ([DFGGR19]), printed p.7 (PDF p.9) of arXiv:2609.10921 (sha256 bc273e88…): at each
step `t`, the retained point `z_t` has density `μ_t`.

**Formalization Note** Stated as a conditional law: given the randomness of steps `< t`, the
probability that `z_t` lies in a Borel set `B` is `∫_{B ∩ [0,1)^d} μ_t`. The strategy is any
`(1 + ε)`-online thinning strategy (`IsThinningDensity`). -/
theorem fact_2_3 (d : ℕ) (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (hin : IsStreamInput P X Ξ Y)
    (μ : ℕ → Ω → (Fin d → ℝ) → ℝ) (hμ : IsThinningDensity ε X Ξ Y μ)
    (t : ℕ) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    P[fun ω => B.indicator (fun _ => (1 : ℝ)) (framePoint ε μ X Ξ Y t ω) | stepSigma X Ξ Y t]
      =ᵐ[P] fun ω => ∫ x in B ∩ cube d, μ t ω x := by sorry

end QMCBeyondHK
