-- Prove2me | Theorems.Thm_WildeQIT_Gentle_lemma_9_4_1
-- name    : WildeQIT.Gentle.lemma_9_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:38.017683+00:00
-- url     : https://prove2.me/theorems/4e4a31f1-7697-499e-bda0-8f7a257ddf38
-- title:
--   Lemma 9.4.1 (Gentle Measurement): $\|\rho-\rho'\|_1\le2\sqrt\varepsilon$
-- statement:
--   Let $\rho$ be a density operator and $\Lambda$ a measurement operator with $0\le\Lambda\le I$ (for instance an element of a POVM). Suppose that $\Lambda$ detects $\rho$ with high probability,
--
--   $$\operatorname{Tr}\{\Lambda\rho\}\ge1-\varepsilon,\qquad \varepsilon\in[0,1].$$
--
--   Then the post-measurement state $\rho'\equiv\sqrt\Lambda\rho\sqrt\Lambda/\operatorname{Tr}\{\Lambda\rho\}$ is $2\sqrt\varepsilon$-close to $\rho$ in trace distance:
--
--   $$\|\rho-\rho'\|_1\le2\sqrt\varepsilon .$$
--
--   A measurement outcome that is very likely disturbs the state only a little. This is the form of the gentle measurement lemma used in the packing and covering arguments later in the book.
--
--   **Formalization Note** $0\le\Lambda\le I$ is positive semidefiniteness of $\Lambda$ and of $I-\Lambda$; $\operatorname{Tr}\{\Lambda\rho\}$, real for such $\Lambda$, is the real part of the complex trace; $\|\cdot\|_1$ is the unhalved published trace norm. The constant is $2\sqrt\varepsilon$; the platform's other gentle measurement statements have the weaker $\sqrt{8\varepsilon}$.
--
--   Differences from the source:
--   - encoding: $\rho'$ defined only when $\operatorname{Tr}\{\Lambda\rho\}>0$ (implicit in (9.196)) → hypothesis $\operatorname{Tr}\{\Lambda\rho\}\neq0$; reason: it excludes only the case, possible only at $\varepsilon=1$, where the book's $\rho'$ is undefined.
--   - encoding: $\operatorname{Tr}\{\Lambda\rho\}$ → real part of the complex trace of $\Lambda\rho$; reason: the trace is real for positive semidefinite $\Lambda,\rho$, so no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.1 (Gentle Measurement), eqs. (9.195)–(9.197), p. 277

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Gentle_postMeasurementState

open Matrix
open scoped MatrixOrder ComplexOrder

namespace WildeQIT.Gentle

/-- **Lemma 9.4.1 (Gentle Measurement)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 277, eqs. (9.195)–(9.197)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then the
post-measurement state `ρ′ = √Λ ρ √Λ / Tr{Λρ}` satisfies `‖ρ − ρ′‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `Tr{Λρ}` is real
for such `Λ` and is taken as the real part of the complex trace. The hypothesis
`Tr{Λρ} ≠ 0` only excludes the case (possible only at `ε = 1`) where the book's `ρ′` is
undefined. `‖·‖₁` is the (unhalved) published `WildeQIT.traceNorm`. -/
theorem lemma_9_4_1 {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re)
    (hne : (Λ * ρ).trace ≠ 0) :
    traceNorm (ρ - postMeasurementState Λ ρ) ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.Gentle
