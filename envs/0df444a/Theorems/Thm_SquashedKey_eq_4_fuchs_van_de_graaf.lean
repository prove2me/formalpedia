-- Prove2me | Theorems.Thm_SquashedKey_eq_4_fuchs_van_de_graaf
-- name    : SquashedKey.eq_4_fuchs_van_de_graaf
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:07.079611+00:00
-- url     : https://prove2.me/theorems/57f35c31-7573-4785-9eda-1e0970227ea8
-- title:
--   Eq. (4) — Fuchs–van de Graaf: $1-\sqrt F\le\frac12\|\rho-\sigma\|_1\le\sqrt{1-F}$
-- statement:
--   For every quantum system (of arbitrary dimension) and all states $\rho,\sigma$ on it,
--   $$
--   1-\sqrt{F(\rho,\sigma)}\ \le\ \tfrac12\|\rho-\sigma\|_1\ \le\ \sqrt{1-F(\rho,\sigma)},
--   $$
--   where $\|\cdot\|_1$ is the trace norm and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ the fidelity.
--
--   The right inequality turns the fidelity hypothesis (44) of Theorem 2 into the trace-distance bound (47).
--
--   **Formalization Note** Both sides are computed in $[0,+\infty]$: the trace norm is the published nuclear norm `traceSize` and the square root is the power $1/2$. Since $0\le F\le 1$ for states, the truncated differences $1-\sqrt F$ and $1-F$ are the real ones.
--
--   Differences from the source:
--
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: 1 − √F(ρ,σ) ≤ ½‖ρ−σ‖₁ ≤ √(1 − F(ρ,σ)) in ℝ → the same two inequalities in ℝ≥0∞, √x as x^(1/2) and truncated subtraction; reason: F ∈ [0,1] and the trace norm of a difference of states is finite, so every term is the real one
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eq. (4), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02

open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Intakenext100.P02 (traceClassSquaredFidelity)

namespace SquashedKey

/-- **Fuchs–van de Graaf inequalities, (4)**, Wilde, *Squashed entanglement and approximate private
states*, arXiv:1606.08028v3, §2.2, (4), p.4 (PDF p.4): "The following inequalities hold for trace
distance and fidelity [FvdG98]: `1 − √F(ρ, σ) ≤ (1/2)‖ρ − σ‖₁ ≤ √(1 − F(ρ, σ))`."

For every type `I` and all states `ρ`, `σ` on `ℓ²(I)`, both inequalities hold.

**Formalization Note** `‖ρ − σ‖₁` is the trace norm `traceSize` and `F` the squared fidelity
`‖√ρ √σ‖₁²` (published `traceClassSquaredFidelity`); both are valued in `ℝ≥0∞` and `√x` is
`x ^ (1/2 : ℝ)`. Since `0 ≤ F ≤ 1` for states, the truncated subtractions `1 − √F` and `1 − F` in
`ℝ≥0∞` are the real differences. -/
theorem eq_4_fuchs_van_de_graaf {I : Type} (ρ σ : State I) :
    1 - traceClassSquaredFidelity ρ σ ^ ((1 : ℝ) / 2) ≤
        traceSize (ρ.coefficients - σ.coefficients) / 2 ∧
      traceSize (ρ.coefficients - σ.coefficients) / 2 ≤
        (1 - traceClassSquaredFidelity ρ σ) ^ ((1 : ℝ) / 2) := by sorry

end SquashedKey
