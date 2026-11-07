-- Prove2me | Theorems.Thm_QMCBeyondHK_lemma_3_4_1
-- name    : QMCBeyondHK.lemma_3_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:12.848546+00:00
-- url     : https://prove2.me/theorems/65b774a3-6448-479f-822f-359ed74e9308
-- title:
--   Lemma 3.4.1 — second moments of Haar discrepancies: $\mathbb E[\varphi_t(H)^2] \le C N_\ell^2/\varepsilon^2$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, $N_\ell = (\ell+1)^d$, and run the Haar-thinning strategy on an independent uniform input stream. For every step $t$ and every $H \in \Pi_{\le\ell}$,
--   $$
--   \mathbb E\big[\varphi_t(H)^2\big] \le C\, \frac{N_\ell^2}{\varepsilon^2} = \tilde O_{d,\varepsilon}(1).
--   $$
--
--   The discrepancies of the low-order Haar functions therefore stay bounded in mean square at every step, which, with Lemma 3.1.1, controls the low-order integration error.
--
--   Differences from the source:
--   - encoding: O(N_ℓ²/ε²) → C · N_ℓ²/ε² with C absolute, chosen before d, ε, n; reason: the meaning of O(·) with an absolute constant
--   - encoding: every step t → every t ∈ ℕ of the run; reason: the run is defined for all t
--   - encoding: expectations and ‖g‖²_B as real numbers → lower Lebesgue integrals and sums in ℝ≥0∞; reason: nonnegative quantities; ℝ≥0∞ has no junk value for a divergent sum or a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Lemma 3.4.1, p.12 (PDF p.14) (footnote 8: Π≤ℓ excludes the constant function)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Lemma 3.4.1 (Second moments of Haar discrepancies), printed p.12 (PDF p.14) of
arXiv:2609.10921 (sha256 bc273e88…): for every step `t` and every `H ∈ Π≤ℓ`,
`E[φ_t(H)²] ≤ O(N_ℓ²/ε²)`.

**Formalization Note** `O(·)` is an absolute constant `C`, chosen before `d, ε, n`; `ℓ = ⌈10 log₂ n⌉`,
`N_ℓ = (ℓ+1)^d`; every step `t ∈ ℕ` of the run. The expectation is a lower Lebesgue integral. -/
theorem lemma_3_4_1 :
    ∃ C : ℝ, ∀ (d : ℕ), 1 ≤ d → ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n : ℕ), 1 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
        IsStreamInput P X Ξ Y → ∀ (t : ℕ), ∀ H ∈ lowOrder d (ell n),
        ∫⁻ ω, ENNReal.ofReal (disc (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) H ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (Nell d (ell n) : ℝ) ^ 2 / ε ^ 2) := by sorry

end QMCBeyondHK
