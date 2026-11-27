-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_9_3_1
-- name    : WildeQIT.Compression.Supplement.theorem_9_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:12:30.025896+00:00
-- url     : https://prove2.me/theorems/6a328cfb-eaad-4fc8-9812-65c88077dc53
-- title:
--   Theorem 9.3.1 (Fuchs–van de Graaf): $1-\sqrt{F(\rho,\sigma)}\le\frac12\|\rho-\sigma\|_1\le\sqrt{1-F(\rho,\sigma)}$
-- statement:
--   Let $\rho,\sigma\in\mathcal D(\mathcal H)$ be density operators, $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ their fidelity and $\|\cdot\|_1$ the trace norm. Then
--
--   $$
--   1-\sqrt{F(\rho,\sigma)}\;\le\;\tfrac12\|\rho-\sigma\|_1\;\le\;\sqrt{1-F(\rho,\sigma)} .
--   $$
--
--   The two inequalities make the trace distance and the fidelity interchangeable measures of closeness: one is small exactly when the other is close to one.
--
--   **Formalization Note** The fidelity is the published squared fidelity and $\|\cdot\|_1$ the published trace norm; both inequalities are asserted.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 9.3.1, p. 274, eq. (9.164)

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 9.3.1, p. 274.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 9.3.1 (Relations between Fidelity and Trace Distance)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 274, (9.164)):
for `ρ, σ ∈ D(H)`, `1 − √F(ρ, σ) ≤ ½‖ρ − σ‖₁ ≤ √(1 − F(ρ, σ))`.

Formalization Note: `F` is the published squared fidelity `‖√ρ√σ‖₁²` (Definition 9.2.3) and
`‖·‖₁` the published trace norm; both inequalities are asserted. -/
theorem theorem_9_3_1 {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 - Real.sqrt (fidelity ρ σ) ≤ (1 / 2 : ℝ) * traceNorm (ρ - σ) ∧
      (1 / 2 : ℝ) * traceNorm (ρ - σ) ≤ Real.sqrt (1 - fidelity ρ σ) := by sorry

end WildeQIT.Compression.Supplement
