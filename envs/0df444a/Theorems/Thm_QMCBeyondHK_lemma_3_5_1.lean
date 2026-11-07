-- Prove2me | Theorems.Thm_QMCBeyondHK_lemma_3_5_1
-- name    : QMCBeyondHK.lemma_3_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:29.766736+00:00
-- url     : https://prove2.me/theorems/4f94308e-5682-4f53-ad6d-762dcf8e771e
-- title:
--   Lemma 3.5.1 — low-order error: $\mathbb E[\mathrm{err}(A,\Pi_{\le\ell}g)^2] \le C N_\ell^2\varepsilon^{-2} n^{-2}\|g\|_B^2$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, $N_\ell = (\ell+1)^d$, and let $A$ be the $n$-point output of the Haar-thinning strategy on an independent uniform input stream. For every $g \in L^2([0,1)^d)$ with $\bar g = 0$,
--   $$
--   \mathbb E\big[\operatorname{err}(A, \Pi_{\le\ell}\, g)^2\big] \le \frac{C\, N_\ell^2}{\varepsilon^2\, n^2}\, \|g\|_B^2 = \frac{\tilde O_{d,\varepsilon}(1)}{n^2}\, \|g\|_B^2 ,
--   $$
--   the expectation being over the randomness of the strategy only.
--
--   This is the bound that gives the $1/n^2$ rate for the low-order Haar component.
--
--   Differences from the source:
--   - generalization: Õ_{d,ε}(1)/n² → C · N_ℓ²/(ε² n²) with an absolute constant C chosen before d, ε, n; reason: an explicit member of Õ_{d,ε}(1) (N_ℓ² = O(log n)^{2d}, poly(1/ε)), the factor that (13) with Lemmas 3.1.1 and 3.4.1 gives; it implies the printed bound
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: expectations and ‖g‖²_B as real numbers → lower Lebesgue integrals and sums in ℝ≥0∞; reason: nonnegative quantities; ℝ≥0∞ has no junk value for a divergent sum or a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Lemma 3.5.1, p.13 (PDF p.15); proof in §3.4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_besovSq
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Lemma 3.5.1 (Low-order error), printed p.13 (PDF p.15) of arXiv:2609.10921
(sha256 bc273e88…): for every `g ∈ L²([0,1)^d)` with `ḡ = 0`,
`E[err(A, Π≤ℓ g)²] ≤ (Õ_{d,ε}(1)/n²) ‖g‖²_B`, the expectation being over the randomness of the
Haar-thinning strategy only.

**Formalization Note** `Õ_{d,ε}(1)` is pinned as `C · N_ℓ²/ε²` with an absolute constant `C`
(chosen before `d, ε, n`), `N_ℓ = (ℓ+1)^d`, `ℓ = ⌈10 log₂ n⌉`. `A` is the `n`-point output; the
expectation is a lower Lebesgue integral and `‖g‖²_B` is in `ℝ≥0∞`. -/
theorem lemma_3_5_1 :
    ∃ C : ℝ, ∀ (d : ℕ), 1 ≤ d → ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n : ℕ), 1 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
        IsStreamInput P X Ξ Y → ∀ (g : (Fin d → ℝ) → ℝ), Measurable g → MemLp g 2 (unif d) →
        cubeMean d g = 0 →
        ∫⁻ ω, ENNReal.ofReal (err (haarOutput d ε n (X · ω) (Ξ · ω) (Y · ω)) (lowProj d (ell n) g) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (Nell d (ell n) : ℝ) ^ 2 / (ε ^ 2 * (n : ℝ) ^ 2)) * besovSq d g := by sorry

end QMCBeyondHK
