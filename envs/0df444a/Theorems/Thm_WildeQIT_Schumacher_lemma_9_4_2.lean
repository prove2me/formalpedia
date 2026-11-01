-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_lemma_9_4_2
-- name    : WildeQIT.Schumacher.lemma_9_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:23.026925+00:00
-- url     : https://prove2.me/theorems/9868efff-f297-4bca-aa10-86f1a0bc8a8f
-- title:
--   Lemma 9.4.2 (Gentle Operator): $\|\rho-\sqrt\Lambda\rho\sqrt\Lambda\|_1 \le 2\sqrt\varepsilon$
-- statement:
--   Let $\rho$ be a density operator and $\Lambda$ a measurement operator, $0 \le \Lambda \le I$. Suppose that
--
--   $$
--   \mathrm{Tr}\{\Lambda\rho\} \ge 1-\varepsilon, \qquad \varepsilon\in[0,1].
--   $$
--
--   Then the unnormalized operator $\sqrt\Lambda\rho\sqrt\Lambda$ is $2\sqrt\varepsilon$-close to $\rho$ in trace norm:
--
--   $$
--   \left\|\rho-\sqrt{\Lambda}\rho\sqrt{\Lambda}\right\|_1 \le 2\sqrt{\varepsilon}.
--   $$
--
--   This is the form used in the direct part of Schumacher compression, with $\Lambda$ the typical projector (eqs. (18.14)–(18.16)).
--
--   **Formalization Note** $0\le\Lambda\le I$ is "$\Lambda$ and $I-\Lambda$ positive semidefinite"; $\sqrt\Lambda$ is `CFC.sqrt`; $\mathrm{Tr}\{\Lambda\rho\}$ is the real part of the complex trace; $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`. The same lemma is also drafted in the series' Gentle Measurement mission (`WildeQIT.Gentle.lemma_9_4_2`).
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.2, eqs. (9.203)–(9.204), p. 278

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix
open scoped MatrixOrder ComplexOrder

namespace WildeQIT.Schumacher

/-- **Lemma 9.4.2 (Gentle Operator)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 278, eqs. (9.203)–(9.204)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then
`‖ρ − √Λ ρ √Λ‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `√Λ` is `CFC.sqrt`;
`Tr{Λρ}` is the real part of the complex trace (real here); `‖·‖₁` is the published
`WildeQIT.traceNorm` (unhalved). -/
theorem lemma_9_4_2 {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re) :
    WildeQIT.traceNorm (ρ - CFC.sqrt Λ * ρ * CFC.sqrt Λ) ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.Schumacher
