-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_corollary_9_1_1
-- name    : WildeQIT.DiamondDist.corollary_9_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:12.932298+00:00
-- url     : https://prove2.me/theorems/2dc77021-0381-4a20-b246-db684d083136
-- title:
--   Corollary 9.1.1 (Measurement on Close States): $\operatorname{Tr}\{\Pi\rho\}\ge\operatorname{Tr}\{\Pi\sigma\}-\tfrac12\|\rho-\sigma\|_1\ge\operatorname{Tr}\{\Pi\sigma\}-\|\rho-\sigma\|_1$
-- statement:
--   Let $\rho,\sigma\in\mathcal D(\mathcal H)$ be density operators on a finite-dimensional Hilbert space and let $\Pi\in\mathcal L(\mathcal H)$ satisfy $0\le\Pi\le I$. Then
--
--   $$
--   \operatorname{Tr}\{\Pi\rho\}\ \ge\ \operatorname{Tr}\{\Pi\sigma\}-\tfrac12\|\rho-\sigma\|_1\ \ge\ \operatorname{Tr}\{\Pi\sigma\}-\|\rho-\sigma\|_1 .
--   $$
--
--   Both inequalities of the chain are part of the statement. The typical use: if a measurement succeeds with probability at least $1-\varepsilon$ on $\sigma$ and $\|\rho-\sigma\|_1\le\varepsilon$, it succeeds with probability at least $1-2\varepsilon$ on $\rho$.
--
--   **Formalization Note** $0\le\Pi\le I$ is $\Pi\succeq0$ and $I-\Pi\succeq0$; the operator is named `P` in Lean. The traces are real for such $\Pi$ and are taken as real parts of complex traces.
--
--   Differences from the source:
--   - encoding: $\operatorname{Tr}\{\Pi\rho\}$, $\operatorname{Tr}\{\Pi\sigma\}$ → real parts of the complex traces; reason: the traces are real when $\Pi\succeq0$ and $\rho,\sigma$ are Hermitian
--   - encoding: states and $\Pi$ on $\mathcal H$ → `Matrix n n ℂ` over a finite index type; reason: the book works in finite dimensions
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 9.1.1, p. 257, eqs. (9.56)–(9.57)

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 9.1.1, p. 257.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.DiamondDist

/-- **Corollary 9.1.1 (Measurement on Close States)** (Wilde, arXiv:1106.1445v8, p. 257,
eqs. (9.56)–(9.57)). For quantum states `ρ, σ ∈ D(H)` and an operator `Π ∈ L(H)` (here `P`) with
`0 ≤ Π ≤ I`: `Tr{Πρ} ≥ Tr{Πσ} − (1/2)‖ρ − σ‖₁ ≥ Tr{Πσ} − ‖ρ − σ‖₁`.

Formalization Note: `0 ≤ Π ≤ I` is `Π.PosSemidef ∧ (1 − Π).PosSemidef`; the traces are real and
taken as real parts. Both inequalities of the chain are stated. -/
theorem corollary_9_1_1 {n : Type} [Fintype n] [DecidableEq n] (ρ σ P : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hP0 : P.PosSemidef) (hP1 : (1 - P).PosSemidef) :
    (P * σ).trace.re - (1 / 2 : ℝ) * traceDist ρ σ ≤ (P * ρ).trace.re ∧ (P * σ).trace.re - traceDist ρ σ ≤ (P * σ).trace.re - (1 / 2 : ℝ) * traceDist ρ σ := by sorry

end WildeQIT.DiamondDist
