-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_theorem_5_3
-- name    : QuantumSymmetryBreaking.CycleColoring.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:48.898013+00:00
-- url     : https://prove2.me/theorems/ad27963a-2c7c-44cd-a83a-59c7e0f57219
-- title:
--   Theorem 5.3 — $2\cdot10^4$-outcome POVMs with $\tfrac1{N^3}\sum_aE(M_a)\le\varepsilon$
-- statement:
--   Fix $q=2\cdot10^4$. For every $\varepsilon>0$ there are a dimension $N\in\mathbb N_+$ and a $q$-outcome POVM $\{M_a\}_{a\in[q]}$ on $\mathbb C^N\otimes\mathbb C^N$ such that
--   $$
--   \frac1{N^3}\sum_{a\in[q]}E(M_a)\le\varepsilon .
--   $$
--   This is the paper's main technical theorem: POVMs with a number of outcomes independent of $\varepsilon$ and arbitrarily small normalized total energy.
--
--   Differences from the source:
--   - encoding: $a\in[q]$, $q=2\cdot10^4$ → `Fin (2 * 10 ^ 4)`; reason: relabelling only (the source's signed colours $\pm i$ relabelled to $[q]$)
--   - encoding: $E(M)=\operatorname{Tr}(AB)$ → the real part of $\operatorname{Tr}(AB)$ (published `energy` at $\Lambda=I$); reason: the trace is real for PSD $M$, the only operators whose energy the statement uses
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Theorem 5.3, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

namespace QuantumSymmetryBreaking.CycleColoring

/-- Theorem 5.3, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.21 (PDF p.24).
Fix `q = 2 · 10^4`. For every `ε > 0` there are `N ∈ ℕ⁺` and a `q`-outcome POVM `{M_a}_{a ∈ [q]}`
on `ℂ^N ⊗ ℂ^N` with `(1/N^3) ∑_a E(M_a) ≤ ε`. -/
theorem theorem_5_3 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ M : Fin (2 * 10 ^ 4) → Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
      IsPOVM M ∧ 1 / (N : ℝ) ^ 3 * ∑ a, energyE (M a) ≤ ε := by sorry

end QuantumSymmetryBreaking.CycleColoring
