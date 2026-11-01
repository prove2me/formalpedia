-- Prove2me | Theorems.Thm_WildeQIT_Gentle_lemma_9_4_3
-- name    : WildeQIT.Gentle.lemma_9_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:46.919211+00:00
-- url     : https://prove2.me/theorems/0ce1ebdb-ee05-4d2e-90fd-aad6ac6bbe32
-- title:
--   Lemma 9.4.3 (Gentle Measurement for Ensembles): $\sum_x p_X(x)\|\rho_x-\sqrt\Lambda\rho_x\sqrt\Lambda\|_1\le2\sqrt\varepsilon$
-- statement:
--   Let $\{p_X(x),\rho_x\}$ be an ensemble of density operators over a finite alphabet $\mathcal X$, with average density operator
--
--   $$\rho\equiv\sum_x p_X(x)\,\rho_x .$$
--
--   Let $\Lambda$ be a positive semidefinite operator with $\Lambda\le I$, and suppose that $\operatorname{Tr}\{\rho\Lambda\}\ge1-\varepsilon$ for some $\varepsilon\in[0,1]$. Then
--
--   $$\sum_x p_X(x)\,\bigl\|\rho_x-\sqrt\Lambda\,\rho_x\,\sqrt\Lambda\bigr\|_1\le2\sqrt\varepsilon .$$
--
--   If an operator detects the average state of an ensemble with high probability, then on average over the ensemble it disturbs the individual states only a little. This is the form in which gentle measurement enters the coding theorems for classical communication over quantum channels.
--
--   **Formalization Note** The finite dimension and the finite alphabet are the book's setting. $p_X$ is the published `WildeQIT.FinDist`; $\Lambda\le I$ is positive semidefiniteness of $I-\Lambda$; $\operatorname{Tr}\{\rho\Lambda\}$ is the real part of the complex trace; $\sqrt\Lambda$ is `CFC.sqrt`; $\|\cdot\|_1$ is the unhalved published trace norm. $\Lambda$ need not belong to a POVM.
--
--   Differences from the source:
--   - encoding: ensemble $\{p_X(x),\rho_x\}$ → a `FinDist` on a finite alphabet and a family of density operators; reason: the book's ensembles have finite alphabets, so the same objects.
--   - encoding: $\operatorname{Tr}\{\rho\Lambda\}$ → real part of the complex trace of $\rho\Lambda$; reason: the trace is real for positive semidefinite $\rho,\Lambda$, so no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.3 (Gentle Measurement for Ensembles), eq. (9.211), p. 279

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_Gentle_averageState

open Matrix
open scoped MatrixOrder ComplexOrder

namespace WildeQIT.Gentle

/-- **Lemma 9.4.3 (Gentle Measurement for Ensembles)** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, p. 279, eq. (9.211)). Let `{p_X(x), ρ_x}` be an ensemble with
average density operator `ρ ≡ ∑_x p_X(x) ρ_x`. Given a positive semi-definite operator `Λ` with
`Λ ≤ I` and `Tr{ρΛ} ≥ 1 − ε` where `ε ∈ [0, 1]`,
`∑_x p_X(x) ‖ρ_x − √Λ ρ_x √Λ‖₁ ≤ 2√ε`.

**Formalization Note.** Finite dimensions and a finite alphabet `𝒳` (a `Fintype`), as throughout
the book. `p_X` is the published `WildeQIT.FinDist`; each `ρ_x` is a density operator. `Λ ≤ I`
is `(1 − Λ).PosSemidef`; `Tr{ρΛ}` is the real part of the complex trace; `√Λ` is `CFC.sqrt Λ`;
`‖·‖₁` is the (unhalved) published `WildeQIT.traceNorm`. `Λ` need not belong to a POVM. -/
theorem lemma_9_4_3 {X n : Type} [Fintype X] [Fintype n] [DecidableEq n]
    (p : FinDist X) (ρ : X → Matrix n n ℂ) (hρ : ∀ x, IsDensityOperator (ρ x))
    (Λ : Matrix n n ℂ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdet : 1 - ε ≤ (averageState p ρ * Λ).trace.re) :
    ∑ x, p.prob x * traceNorm (ρ x - CFC.sqrt Λ * ρ x * CFC.sqrt Λ) ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.Gentle
