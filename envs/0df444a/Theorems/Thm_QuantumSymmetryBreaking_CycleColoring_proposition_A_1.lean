-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_proposition_A_1
-- name    : QuantumSymmetryBreaking.CycleColoring.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:31.282929+00:00
-- url     : https://prove2.me/theorems/dd32798f-221f-4b59-86c5-e5d255195ff8
-- title:
--   Proposition A.1 — $E(M)\le4N\|\Gamma-\sqrt Z\|_F^2$ for zero-energy $Z$
-- statement:
--   Let $Z\in L(\mathbb C^N\otimes\mathbb C^N)$ be PSD with $E(Z)=0$. Then:
--
--   1. for every PSD $M$ with $0\preceq M\preceq I$ and every factorization $M=\Gamma^\dagger\Gamma$ with $\Gamma\in L(\mathbb C^N\otimes\mathbb C^N)$,
--   $$
--   E(M)\le4N\,\|\Gamma-\sqrt Z\|_F^2 ;
--   $$
--   2. in particular (taking $\Gamma=\sqrt M$), $E(M)\le4N\|\sqrt M-\sqrt Z\|_F^2$ for every such $M$.
--
--   Here $\sqrt{\cdot}$ is the PSD square root. The proposition bounds the energy of an operator by its distance to a zero-energy one, which drives the normalization Lemma 5.6.
--
--   Differences from the source:
--   - encoding: $\sqrt Z$, $\sqrt M$ and $0\preceq M\preceq I$ → `cfc Real.sqrt` (continuous functional calculus) and PSD-ness of $M$ and $I-M$; reason: on PSD matrices `cfc Real.sqrt` is the PSD square root
--   - encoding: $E(M)=\operatorname{Tr}(AB)$ → the real part of $\operatorname{Tr}(AB)$ (published `energy` at $\Lambda=I$); reason: the trace is real for PSD $M$, the only operators whose energy the statement uses
--   - encoding: $\mathbb C^N$ with $N\in\mathbb N_+$ → `Fin N` for any natural $N$; reason: at $N=0$ every operator is the empty matrix and the statement is trivially true; no instance with $N\ge1$ changes
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Proposition A.1, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open QuantumCycleColoring.FourColor
open scoped ComplexOrder
open Matrix

namespace QuantumSymmetryBreaking.CycleColoring

/-- Proposition A.1, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.42 (PDF p.45).
Let `Z ∈ L(ℂ^N ⊗ ℂ^N)` be PSD with `E(Z) = 0`. For every `M` with `0 ⪯ M ⪯ I` and every factorization
`M = Γ†Γ`, `E(M) ≤ 4N ‖Γ − √Z‖_F^2`; in particular `E(M) ≤ 4N ‖√M − √Z‖_F^2`. -/
theorem proposition_A_1 {N : ℕ} (Z : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (hZ : Z.PosSemidef)
    (hZE : energyE Z = 0) :
    (∀ M Γ : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ, M.PosSemidef → (1 - M).PosSemidef →
      M = Γᴴ * Γ → energyE M ≤ 4 * N * frobNorm (Γ - cfc Real.sqrt Z) ^ 2) ∧
    (∀ M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ, M.PosSemidef → (1 - M).PosSemidef →
      energyE M ≤ 4 * N * frobNorm (cfc Real.sqrt M - cfc Real.sqrt Z) ^ 2) := by sorry

end QuantumSymmetryBreaking.CycleColoring
