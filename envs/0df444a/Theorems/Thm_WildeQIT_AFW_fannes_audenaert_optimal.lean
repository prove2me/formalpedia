-- Prove2me | Theorems.Thm_WildeQIT_AFW_fannes_audenaert_optimal
-- name    : WildeQIT.AFW.fannes_audenaert_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:25.599802+00:00
-- url     : https://prove2.me/theorems/592f541e-c6c8-4f80-ab20-1459dedeea53
-- title:
--   Theorem 11.10.2 (Fannes–Audenaert): $|H(\rho)-H(\sigma)| \le T\log(d-1) + h_2(T)$, and the bound is attained (corrected: optimality at dimension 1 only for T = 0)
-- statement:
--   Let $\rho,\sigma$ be density operators on a Hilbert space $\mathcal H$ of dimension $d$, and let $T \equiv \tfrac12\|\rho-\sigma\|_1$ be their trace distance. Write $H$ for the von Neumann entropy and $h_2$ for the binary entropy (base-2 logarithms). Then
--
--   1. the inequality
--   $$
--   |H(\rho)-H(\sigma)| \le T\log(d-1) + h_2(T)
--   $$
--   holds;
--   2. the bound is optimal: for every dimension $d \ge 1$ and every $T\in[0,1]$, with $T = 0$ when $d = 1$, there are density operators $\rho,\sigma$ on a $d$-dimensional space with $\tfrac12\|\rho-\sigma\|_1 = T$ and
--   $$
--   |H(\rho)-H(\sigma)| = T\log(d-1) + h_2(T) .
--   $$
--
--   Unlike Theorem 11.10.1, the bound is stated at the exact trace distance, with no case split, and it cannot be improved for any value of the distance or of the dimension.
--
--   **Formalization Note** $\mathcal H$ is a finite index type with $d$ its cardinality; `WildeQIT.IsDensityOperator`, `WildeQIT.traceNorm`, `QAlgorithms.vnEntropy`, `WildeQIT.binaryEntropy`. Both clauses are universally quantified over the finite type, so the theorem is a conjunction of two statements.
--
--   Differences from the source:
--   - correction: optimality "for all $T \in [0,1]$ and dimension $\dim(\mathcal H)$" → for every $d \ge 2$ and every $T \in [0,1]$, and for $d = 1$ only at $T = 0$; reason: counterexample $d = 1$, $T = 1/2$: the only density operator on a one-dimensional space is $(1)$, so every pair has $\tfrac12\|\rho-\sigma\|_1 = 0 \ne 1/2$.
--   - reading: "there exists a pair of states that saturates it for all $T$" → for every $T$ there is a pair; reason: the trace distance of a fixed pair is a single number, and the book's witness, $\rho = |0\rangle\langle 0|$ and $\sigma = (1-\varepsilon)|0\rangle\langle0| + \frac{\varepsilon}{d-1}\sum_{i\ge1}|i\rangle\langle i|$, depends on $T = \varepsilon$.
--   - encoding: at $d = 1$ the term $T\log(d-1)$ has $\log 0$ → `Real.logb 2 0 = 0`; reason: at $d = 1$, $T = 0$ and the book's term is $0\cdot\log 0$, read as $0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.2, (11.245), p. 358; optimality witness, p. 359

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_binaryEntropy

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.2
(Fannes–Audenaert Inequality), p. 358: "Let ρ, σ ∈ D(H) and let T ≡ ½∥ρ − σ∥₁. Then the following
inequality holds |H(ρ) − H(σ)| ≤ T log[dim(H) − 1] + h₂(T). (11.245) Furthermore, this bound is
optimal because there exists a pair of states that saturates it for all T ∈ [0, 1] and dimension
dim(H)."

The first conjunct is (11.245); the second is the optimality clause: for every dimension
`d ≥ 1` and every `T ∈ [0, 1]` (with `T = 0` when `d = 1`) there are states at trace distance `T`
attaining the bound.

**Formalization Note.** `H` is a finite index type with `dim(H) = card ι`; `D(H)` is
`WildeQIT.IsDensityOperator`, `∥·∥₁` is `WildeQIT.traceNorm`, `H(·)` is `QAlgorithms.vnEntropy`,
`h₂` is `WildeQIT.binaryEntropy`, all base 2. In dimension 1 every two states are equal, so
`T = 0` is the only distance; the optimality clause there is stated for `T = 0` only (the printed
"for all T ∈ [0, 1] and dimension" fails at `d = 1`, `T > 0`). -/
theorem fannes_audenaert_optimal :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ),
        WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
        |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤
          WildeQIT.traceNorm (ρ - σ) / 2 * Real.logb 2 ((Fintype.card ι : ℝ) - 1) +
            WildeQIT.binaryEntropy (WildeQIT.traceNorm (ρ - σ) / 2)) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι →
      ∀ T : ℝ, 0 ≤ T → T ≤ 1 → (2 ≤ Fintype.card ι ∨ T = 0) →
        ∃ ρ σ : Matrix ι ι ℂ, WildeQIT.IsDensityOperator ρ ∧ WildeQIT.IsDensityOperator σ ∧
          WildeQIT.traceNorm (ρ - σ) / 2 = T ∧
          |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| =
            T * Real.logb 2 ((Fintype.card ι : ℝ) - 1) + WildeQIT.binaryEntropy T) := by sorry

end WildeQIT.AFW
