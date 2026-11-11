-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_6_7
-- name    : QuantumCycleColoring.FourColor.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:14.770854+00:00
-- url     : https://prove2.me/theorems/112419c0-f0da-4cbe-8860-282242cec762
-- title:
--   Lemma 6.7: one outcome with exact zero energy and maximal mass forces constant total energy
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $\{P_i\}_{i\in[4]}$ be a 4-outcome POVM on $\mathbb C^N\otimes\mathbb C^N$ and $\Lambda$ a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$. If
--   $$m_\Lambda(P_1)=\tfrac14\quad\text{and}\quad\mathcal E_\Lambda(P_1)=0,$$
--   then
--   $$\sum_{i=1}^4\mathcal E_\Lambda(P_i)\ge c .$$
--
--   This is the exact special case of the four-colour theorem that the stability theorem later makes robust.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: outcomes i ∈ [4] = {1,2,3,4}, the distinguished one being P_1 → outcomes Fin 4 = {0,1,2,3}, the distinguished one being P 0; reason: 0-based indexing; the same POVMs
--   - reading: ∑_{i=1}^4 E_Λ(P_i) = Ω(1) → one explicit constant ∃ K > 0 quantified before every other object (dimension, operators, Λ); reason: the paper's O(·)/Ω(1) constants are absolute; this is the strongest reading
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 6.7, p.44

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 6.7, p.44 (Gur–Li, STOC 2027 #515). There is a universal `c > 0` such that: for
every 4-outcome POVM `{P_i}` on `ℂ^d ⊗ ℂ^d` and PSD `Λ` with `‖Λ‖_F = 1`, if `m_Λ(P_1) = 1/4` and
`E_Λ(P_1) = 0`, then `∑_{i=1}^4 E_Λ(P_i) ≥ c`. Outcome `1` of the paper is `0 : Fin 4`. -/
theorem lemma_6_7 : ∃ c : ℝ, 0 < c ∧
    ∀ (d : Type) [Fintype d] [DecidableEq d] (P : Fin 4 → Matrix (d × d) (d × d) ℂ),
      FuchsVdGraaf.IsPOVM P →
      ∀ (Λ : Matrix d d ℂ), Λ.PosSemidef → frobNorm Λ = 1 →
      mass Λ (P 0) = 1 / 4 → energy Λ (P 0) = 0 →
      c ≤ ∑ i, energy Λ (P i) := by sorry

end QuantumCycleColoring.FourColor
