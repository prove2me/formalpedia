-- Prove2me | Theorems.Thm_QMCBeyondHK_lemma_3_5_3
-- name    : QMCBeyondHK.lemma_3_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:33.607666+00:00
-- url     : https://prove2.me/theorems/161df4f1-b6f2-43b5-bd12-b955a02a478c
-- title:
--   Lemma 3.5.3 — orthogonality of increments: $\mathbb E_{t-1}[h(z_t)] = 0$, $\mathbb E_{t-1}[h(z_t)^2] \le (1+\varepsilon/2)\|h\|_2^2$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, let $(z_t)$ be the points retained by the Haar-thinning strategy on an independent uniform input stream, $A = (z_0,\dots,z_{n-1})$ its output, and $\mathbb E_{t-1}$ the conditional expectation given the randomness of steps $\le t-1$. Let $g \in L^2([0,1)^d)$ and set $h := \Pi_{>\ell}\, g$. For every step $t$, $h(z_t)$ and $h(z_t)^2$ are integrable and
--   $$
--   \mathbb E_{t-1}\big[h(z_t)\big] = 0 \qquad\text{and}\qquad \mathbb E_{t-1}\big[h(z_t)^2\big] \le \Big(1 + \frac{\varepsilon}{2}\Big)\|h\|_2^2 \quad \text{a.s.}
--   $$
--   Consequently,
--   $$
--   \mathbb E\big[\operatorname{err}(A, h)^2\big] = \frac{1}{n^2} \sum_{t=0}^{n-1} \mathbb E\big[h(z_t)^2\big] \le \frac{1 + \varepsilon/2}{n}\, \|h\|_2^2 .
--   $$
--
--   The target densities are orthogonal to high-order Haar functions, so the high-order error behaves like a martingale with the Monte Carlo rate.
--
--   Differences from the source:
--   - encoding: E_{t−1}[·], the expectation conditioned on the randomness of the strategy in steps ≤ t − 1 → the conditional expectation given σ(x_u, ξ_u, y_u : u < t), with the integrability of h(z_t) and h(z_t)² asserted; reason: the same σ-algebra; the integrability rules out junk conditional expectations
--   - encoding: Π>ℓ g, the orthogonal projection onto the span of the remaining non-constant Haar functions → the pointwise function g − ḡ − Π≤ℓ g; reason: the Haar functions form an orthogonal basis, so this is that projection, as an everywhere-defined representative
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: the unconditional expectations of the consequence → lower Lebesgue integrals in ℝ≥0∞; reason: nonnegative quantities; no junk value
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Lemma 3.5.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Lemma 3.5.3 (Orthogonality of increments), printed p.14 (PDF p.16) of arXiv:2609.10921
(sha256 bc273e88…): set `h := Π>ℓ g`. For every step `t`, `E_{t−1}[h(z_t)] = 0` and
`E_{t−1}[h(z_t)²] ≤ (1 + ε/2)‖h‖₂²`. Consequently,
`E[err(A, h)²] = (1/n²) ∑_{t=0}^{n−1} E[h(z_t)²] ≤ ((1 + ε/2)/n) ‖h‖₂²`.

**Formalization Note** `E_{t−1}` is the conditional expectation given `stepSigma t`, the
randomness of steps `≤ t − 1`; `h(z_t)` and `h(z_t)²` are stated integrable, so neither conditional
expectation is a junk value. `Π>ℓ g` is the pointwise `g − ḡ − Π≤ℓ g`, `ℓ = ⌈10 log₂ n⌉`. The
unconditional expectations of the consequence are lower Lebesgue integrals. -/
theorem lemma_3_5_3 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (hin : IsStreamInput P X Ξ Y)
    (g : (Fin d → ℝ) → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 (unif d)) :
    (∀ t : ℕ,
      Integrable (fun ω => highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t)) P ∧
      Integrable (fun ω => highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) ^ 2) P ∧
      P[fun ω => highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t)
          | stepSigma X Ξ Y t] =ᵐ[P] 0 ∧
      P[fun ω => highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) ^ 2
          | stepSigma X Ξ Y t]
        ≤ᵐ[P] fun _ => (1 + ε / 2) * ∫ x in cube d, highProj d (ell n) g x ^ 2) ∧
    ∫⁻ ω, ENNReal.ofReal (err (haarOutput d ε n (X · ω) (Ξ · ω) (Y · ω)) (highProj d (ell n) g) ^ 2) ∂P
      = (∑ t ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal
          (highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) ^ 2) ∂P)
          / ((n : ℝ≥0∞) ^ 2) ∧
    (∑ t ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal
          (highProj d (ell n) g (haarPoint d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) ^ 2) ∂P)
          / ((n : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal ((1 + ε / 2) / n * ∫ x in cube d, highProj d (ell n) g x ^ 2) := by sorry

end QMCBeyondHK
