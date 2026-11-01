-- Prove2me | Theorems.Thm_WildeQIT_AFW_mutualInfo_bounds
-- name    : WildeQIT.AFW.mutualInfo_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:59.426512+00:00
-- url     : https://prove2.me/theorems/2c56f728-9554-48d6-9018-e9e0a0cdd040
-- title:
--   Theorem 11.10.4: $\frac{2}{\ln 2}\Delta^2 \le I(A;B)_\rho \le 2\Delta\log\min\{d_A,d_B\} + g_2(\Delta)$
-- statement:
--   Let $\rho_{AB}$ be a density operator on $\mathcal H_A\otimes\mathcal H_B$ with marginals $\rho_A,\rho_B$, and let
--
--   $$
--   \Delta \equiv \tfrac12\,\|\rho_{AB} - \rho_A\otimes\rho_B\|_1
--   $$
--
--   be its trace distance from the product of its marginals. Then, with $I(A;B)_\rho$ the quantum mutual information (base-2 logarithms) and $g_2(\Delta) = (\Delta+1)\log_2(\Delta+1) - \Delta\log_2\Delta$,
--
--   $$
--   I(A;B)_\rho \ge \frac{2}{\ln 2}\,\Delta^2 ,
--   $$
--
--   $$
--   I(A;B)_\rho \le 2\Delta\log\bigl[\min\{\dim(\mathcal H_A),\dim(\mathcal H_B)\}\bigr] + g_2(\Delta) .
--   $$
--
--   These refine non-negativity of the mutual information and the dimension bound on it: the mutual information is small exactly when the state is close to a product state, with explicit rates in both directions.
--
--   **Formalization Note** The bipartite space is `A × B`; $\rho_A$ and $\rho_B$ are `WildeQIT.partialTraceRight ρ` and `WildeQIT.partialTraceLeft ρ`, $\otimes$ is the Kronecker product, $\|\cdot\|_1$ is `WildeQIT.traceNorm`, $I(A;B)$ is `WildeQIT.AFW.qMutualInfo`, $\ln 2$ is `Real.log 2`. $\Delta$ is a real variable fixed by its defining equation.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.4, (11.276)–(11.277), p. 361

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_AFW_g2
import Definitions.Def_WildeQIT_AFW_qMutualInfo

open scoped Kronecker

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.4, p. 361:
"Let ρ_AB ∈ D(H_A ⊗ H_B) and let ∆ ≡ ½∥ρ_AB − ρ_A ⊗ ρ_B∥₁. Then
I(A; B) ≥ (2/ln 2) ∆², (11.276)
I(A; B)_ρ ≤ 2∆ log[min{dim(H_A), dim(H_B)}] + g₂(∆). (11.277)"

**Formalization Note.** `H_A ⊗ H_B` is the index type `A × B`; `ρ_A = Tr_B ρ` is
`WildeQIT.partialTraceRight ρ`, `ρ_B = Tr_A ρ` is `WildeQIT.partialTraceLeft ρ`, and `⊗` is the
Kronecker product. `D(H)` is `WildeQIT.IsDensityOperator`, `∥·∥₁` is `WildeQIT.traceNorm`,
`I(A; B)` is `WildeQIT.AFW.qMutualInfo` (base 2), `log` is `log₂`, and `ln 2 = Real.log 2`. `∆`
is a binder pinned by its defining equation `hΔ`. -/
theorem mutualInfo_bounds {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (Δ : ℝ)
    (hΔ : Δ = WildeQIT.traceNorm
      (ρ - WildeQIT.partialTraceRight ρ ⊗ₖ WildeQIT.partialTraceLeft ρ) / 2) :
    2 / Real.log 2 * Δ ^ 2 ≤ qMutualInfo ρ ∧
    qMutualInfo ρ ≤
      2 * Δ * Real.logb 2 (min (Fintype.card A) (Fintype.card B) : ℕ) + g2 Δ := by sorry

end WildeQIT.AFW
