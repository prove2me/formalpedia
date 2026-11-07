-- Prove2me | Theorems.Thm_QMCBeyondHK_lemma_3_5_2
-- name    : QMCBeyondHK.lemma_3_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:29.657923+00:00
-- url     : https://prove2.me/theorems/3760917e-135a-4e2c-8a2d-4e9de3ce4bcb
-- title:
--   Lemma 3.5.2 — high-order error: $\mathbb E[\mathrm{err}(A,\Pi_{>\ell}g)^2] \le (2^{1-\ell}/n)\|g\|_B^2 \le (2/n^{11})\|g\|_B^2$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, and let $A$ be the $n$-point output of the Haar-thinning strategy on an independent uniform input stream. For every $g \in L^2([0,1)^d)$,
--   $$
--   \mathbb E\big[\operatorname{err}(A, \Pi_{>\ell}\, g)^2\big] \le \frac{2^{1-\ell}}{n}\, \|g\|_B^2 \le \frac{2}{n^{11}}\, \|g\|_B^2 ,
--   $$
--   the expectation being over the randomness of the strategy only.
--
--   The high-order component is negligible: its error is smaller than any fixed power of $1/n$ needed in Theorem 1.2.
--
--   Differences from the source:
--   - generalization: (1/poly(n)) ‖g‖²_B → (2/n^11) ‖g‖²_B; reason: an explicit inverse polynomial: ℓ ≥ 10 log₂ n gives 2^{1−ℓ}/n ≤ 2/n^{11}; it implies the printed bound
--   - encoding: Π>ℓ g, the orthogonal projection onto the span of the remaining non-constant Haar functions → the pointwise function g − ḡ − Π≤ℓ g; reason: the Haar functions form an orthogonal basis, so this is that projection, as an everywhere-defined representative
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: expectations and ‖g‖²_B as real numbers → lower Lebesgue integrals and sums in ℝ≥0∞; reason: nonnegative quantities; ℝ≥0∞ has no junk value for a divergent sum or a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Lemma 3.5.2, p.13 (PDF p.15); proof in §3.4.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_besovSq
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Lemma 3.5.2 (High-order error), printed p.13 (PDF p.15) of arXiv:2609.10921
(sha256 bc273e88…): for every `g ∈ L²([0,1)^d)`,
`E[err(A, Π>ℓ g)²] ≤ (2^{1−ℓ}/n) ‖g‖²_B ≤ (1/poly(n)) ‖g‖²_B`, the expectation being over the
randomness of the Haar-thinning strategy only.

**Formalization Note** `ℓ = ⌈10 log₂ n⌉`; `1/poly(n)` is pinned as `2/n^{11}` (from `2^{−ℓ} ≤ n^{−10}`).
`Π>ℓ g` is the pointwise `g − ḡ − Π≤ℓ g`; the expectation is a lower Lebesgue integral. -/
theorem lemma_3_5_2 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (hin : IsStreamInput P X Ξ Y)
    (g : (Fin d → ℝ) → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 (unif d)) :
    ∫⁻ ω, ENNReal.ofReal (err (haarOutput d ε n (X · ω) (Ξ · ω) (Y · ω)) (highProj d (ell n) g) ^ 2) ∂P
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 - (ell n : ℤ)) / n) * besovSq d g ∧
      ENNReal.ofReal ((2 : ℝ) ^ (1 - (ell n : ℤ)) / n) * besovSq d g
        ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 11) * besovSq d g := by sorry

end QMCBeyondHK
