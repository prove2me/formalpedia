-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_lemma_9_4_1
-- name    : WildeQIT.Schumacher.lemma_9_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:26.373914+00:00
-- url     : https://prove2.me/theorems/da967aa9-4237-49a0-89bd-d529148af573
-- title:
--   Lemma 9.4.1 (Gentle Measurement): $\|\rho-\rho'\|_1 \le 2\sqrt\varepsilon$
-- statement:
--   Let $\rho$ be a density operator and $\Lambda$ a measurement operator, $0 \le \Lambda \le I$. Suppose that $\Lambda$ detects $\rho$ with high probability,
--
--   $$
--   \mathrm{Tr}\{\Lambda\rho\} \ge 1-\varepsilon, \qquad \varepsilon\in[0,1].
--   $$
--
--   Then the post-measurement state $\rho' = \sqrt\Lambda\rho\sqrt\Lambda/\mathrm{Tr}\{\Lambda\rho\}$ is $2\sqrt\varepsilon$-close to $\rho$ in trace norm:
--
--   $$
--   \|\rho-\rho'\|_1 \le 2\sqrt{\varepsilon}.
--   $$
--
--   A measurement outcome that is very likely disturbs the state only slightly.
--
--   **Formalization Note** $0\le\Lambda\le I$ is "$\Lambda$ and $I-\Lambda$ positive semidefinite"; $\mathrm{Tr}\{\Lambda\rho\}$ is the real part of the complex trace (real here); $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`, unnormalized. The same lemma is also drafted in the series' Gentle Measurement mission (`WildeQIT.Gentle.lemma_9_4_1`); drafts cannot import drafts.
--
--   Differences from the source:
--   - encoding: Tr{Λρ} ≥ 1 − ε with ε ∈ [0, 1] → additionally Tr{Λρ} ≠ 0; reason: excludes only the case (possible only at ε = 1) where the book's ρ′ is undefined.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.1, eqs. (9.195)–(9.197), p. 277

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Gentle_postMeasurementState

open Matrix
open scoped MatrixOrder ComplexOrder

namespace WildeQIT.Schumacher

/-- **Lemma 9.4.1 (Gentle Measurement)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 277, eqs. (9.195)–(9.197)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then the
post-measurement state `ρ′ = √Λ ρ √Λ / Tr{Λρ}` satisfies `‖ρ − ρ′‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `Tr{Λρ}` is the real
part of the complex trace (real here). The hypothesis `Tr{Λρ} ≠ 0` only excludes the case
(possible only at `ε = 1`) where the book's `ρ′` is undefined. `‖·‖₁` is the published
`WildeQIT.traceNorm` (unhalved). -/
theorem lemma_9_4_1 {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re)
    (hne : (Λ * ρ).trace ≠ 0) :
    WildeQIT.traceNorm (ρ - WildeQIT.Gentle.postMeasurementState Λ ρ) ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.Schumacher
