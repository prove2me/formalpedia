-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_5_5
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:18.570993+00:00
-- url     : https://prove2.me/theorems/30fa861a-0e13-48c7-b776-12c097f1adcb
-- title:
--   Lemma 5.5 — $E(M)=0$ iff $\operatorname{supp}(M)\subseteq V\otimes\overline{V^\perp}$
-- statement:
--   Let $M\in L(\mathbb C^N\otimes\mathbb C^N)$ be PSD and let $E(M)=\operatorname{Tr}(\operatorname{Tr}_A(M)^\top\operatorname{Tr}_B(M))$ be its energy. The following are equivalent:
--
--   1. $M$ has zero energy, $E(M)=0$;
--   2. there is an orthogonal decomposition $V\oplus V^\perp=\mathbb C^N$ such that
--   $$
--   \operatorname{supp}(M)\subseteq V\otimes\overline{V^\perp},
--   $$
--   where $V\otimes\overline{V^\perp}=\operatorname{span}\{x\otimes\bar y:x\in V,\ y\in V^\perp\}$.
--
--   This characterizes the zero-energy operators, i.e. the POVM elements that never produce a monochromatic edge (a corollary of Gur–Li 2026, Lemma 5.3).
--
--   Differences from the source:
--   - encoding: $\operatorname{supp}(M)$ and $V\otimes\overline{V^\perp}$ → the range of $M$ as a linear map, and the published `cutSpace V`; reason: for Hermitian $M$ the support is its range; `cutSpace V` is the span of $x\otimes\bar y$, $x\in V$, $y\in V^\perp$
--   - encoding: $E(M)=\operatorname{Tr}(AB)$ → the real part of $\operatorname{Tr}(AB)$ (published `energy` at $\Lambda=I$); reason: the trace is real for PSD $M$, the only operators whose energy the statement uses
--   - encoding: $\mathbb C^N$ with $N\in\mathbb N_+$ → `Fin N` for any natural $N$; reason: at $N=0$ every operator is the empty matrix and the statement is trivially true; no instance with $N\ge1$ changes
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 5.5, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open QuantumCycleColoring.FourColor
open scoped ComplexOrder

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 5.5, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.22 (PDF p.25).
For a PSD `M ∈ L(ℂ^N ⊗ ℂ^N)`: `E(M) = 0` if and only if there is a subspace `V ⊆ ℂ^N`
(an orthogonal decomposition `V ⊕ V^⊥ = ℂ^N`) with `supp(M) ⊆ V ⊗ \overline{V^⊥}`. -/
theorem lemma_5_5 {N : ℕ} (M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (hM : M.PosSemidef) :
    energyE M = 0 ↔ ∃ V : Submodule ℂ (EuclideanSpace ℂ (Fin N)),
      LinearMap.range (Matrix.toEuclideanLin M) ≤ cutSpace V := by sorry

end QuantumSymmetryBreaking.CycleColoring
