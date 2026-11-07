-- Prove2me | Theorems.Thm_QMCBeyondHK_observation_3_1
-- name    : QMCBeyondHK.observation_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:05.225826+00:00
-- url     : https://prove2.me/theorems/5a0203f7-01c7-4cc4-bff2-943f4e58659a
-- title:
--   Observation 3.1 — shifting the points is shifting the function: $\mathbb E[\mathrm{err}(A_s,f)^2] = \mathbb E_s\mathbb E[\mathrm{err}(A,f_s)^2]$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, and let $s, (x_t,\xi_t,y_t)$ be an independent uniform shift and input stream. Let $A_s$ be the output of the uniformly-shifted Haar-thinning algorithm, and $A$ the output of the (unshifted) Haar-thinning strategy on the same stream. For every $f \in L^2([0,1)^d)$,
--   $$
--   \mathbb E\big[\operatorname{err}(A_s, f)^2\big] = \mathbb E_{s'}\Big[\mathbb E\big[\operatorname{err}(A, f_{s'})^2\big]\Big], \tag{9}
--   $$
--   where on the right the inner expectation is over the randomness of the unshifted strategy for a fixed shift $s'$, and the outer one over $s' \sim \mathrm{Unif}[0,1)^d$.
--
--   It reduces the analysis of the shifted algorithm to that of plain Haar-thinning applied to shifted functions.
--
--   Differences from the source:
--   - encoding: g ∈ L²([0,1)^d) → a measurable g : ℝ^d → ℝ with MemLp g 2 on the cube; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: expectations and ‖g‖²_B as real numbers → lower Lebesgue integrals and sums in ℝ≥0∞; reason: nonnegative quantities; ℝ≥0∞ has no junk value for a divergent sum or a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying a measurable uniform shift and input stream, all mutually independent (IsShiftedStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Observation 3.1, eq. (9), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Observation 3.1 (Shifting the function), printed p.9 (PDF p.11) of arXiv:2609.10921
(sha256 bc273e88…): for every `f ∈ L²([0,1)^d)`, `E[err(A_s, f)²] = E_s[E[err(A, f_s)²]]`, where the
inner expectation is over the (unshifted) Haar-thinning strategy for a fixed shift `s`.

**Formalization Note** Expectations are lower Lebesgue integrals in `ℝ≥0∞`; `E_s` is the integral
over `s ∈ [0,1)^d` against Lebesgue measure. -/
theorem observation_3_1 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Ω → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hin : IsShiftedStreamInput P s X Ξ Y)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 (unif d)) :
    ∫⁻ ω, ENNReal.ofReal (err (shiftedOutput d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω)) f ^ 2) ∂P
      = ∫⁻ s' in cube d,
          (∫⁻ ω, ENNReal.ofReal (err (haarOutput d ε n (X · ω) (Ξ · ω) (Y · ω)) (shiftFun f s') ^ 2) ∂P) := by sorry

end QMCBeyondHK
