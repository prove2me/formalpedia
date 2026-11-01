-- Prove2me | Theorems.Thm_WildeQIT_Gentle_lemma_9_4_2
-- name    : WildeQIT.Gentle.lemma_9_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:10.976438+00:00
-- url     : https://prove2.me/theorems/c30d723c-1f29-455d-bf4e-84ea26e31ea8
-- title:
--   Lemma 9.4.2 (Gentle Operator): $\|\rho-\sqrt\Lambda\rho\sqrt\Lambda\|_1\le2\sqrt\varepsilon$
-- statement:
--   Let $\rho$ be a density operator and $\Lambda$ a measurement operator with $0\le\Lambda\le I$. Suppose that
--
--   $$\operatorname{Tr}\{\Lambda\rho\}\ge1-\varepsilon,\qquad \varepsilon\in[0,1].$$
--
--   Then the unnormalized operator $\sqrt\Lambda\rho\sqrt\Lambda$ is $2\sqrt\varepsilon$-close to $\rho$ in trace norm:
--
--   $$\bigl\|\rho-\sqrt\Lambda\,\rho\,\sqrt\Lambda\bigr\|_1\le2\sqrt\varepsilon .$$
--
--   This variant of the gentle measurement lemma avoids dividing by the success probability and is the single-state case of Lemma 9.4.3.
--
--   **Formalization Note** $0\le\Lambda\le I$ is positive semidefiniteness of $\Lambda$ and of $I-\Lambda$; $\sqrt\Lambda$ is `CFC.sqrt`; $\|\cdot\|_1$ is the unhalved published trace norm. The constant is $2\sqrt\varepsilon$, sharper than the $\sqrt{8\varepsilon}$ of the platform statements `WinterExtrinsic.lemma_4` and `Renew46.P43.tenderOperator`.
--
--   Differences from the source:
--   - encoding: $\operatorname{Tr}\{\Lambda\rho\}$ → real part of the complex trace of $\Lambda\rho$; reason: the trace is real for positive semidefinite $\Lambda,\rho$, so no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.2 (Gentle Operator), eqs. (9.203)–(9.204), p. 278

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix
open scoped MatrixOrder ComplexOrder

namespace WildeQIT.Gentle

/-- **Lemma 9.4.2 (Gentle Operator)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 278, eqs. (9.203)–(9.204)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then
`‖ρ − √Λ ρ √Λ‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `Tr{Λρ}` is the
real part of the complex trace of `Λ * ρ`; `√Λ` is `CFC.sqrt Λ`; `‖·‖₁` is the (unhalved)
published `WildeQIT.traceNorm`. The constant is `2√ε`, not the `√(8ε)` of other sources. -/
theorem lemma_9_4_2 {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re) :
    traceNorm (ρ - CFC.sqrt Λ * ρ * CFC.sqrt Λ) ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.Gentle
