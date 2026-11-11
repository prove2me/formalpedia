-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_theorem_5_6
-- name    : QuantumCycleColoring.FourColor.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:20.150193+00:00
-- url     : https://prove2.me/theorems/9b607fcd-6755-4e00-939e-8fb8234b0098
-- title:
--   Theorem 5.6: stability of operators with maximal mass and small energy
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $N\ge2$, let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and let $\Lambda$ be a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$ (not necessarily positive definite). If $\mathcal E_\Lambda(P)=\varepsilon\ge0$ and $m_\Lambda(P)=\tfrac14$, then there are a PSD $P'$ with $0\preceq P'\preceq I$ and a PSD $\Lambda'$ with $\|\Lambda'\|_F=1$ such that
--   $$\mathcal E_{\Lambda'}(P')=0,\qquad m_{\Lambda'}(P')=\tfrac14,\qquad \|\Lambda-\Lambda'\|_F^2\le K\varepsilon^{1/4},\qquad \|P-P'\|_\Lambda\le K\varepsilon^{1/4}.$$
--
--   This is the robust version of Theorem 5.1: an operator of maximal mass and small energy, together with its weight, is close to an exact zero-energy extremizer.
--
--   **Formalization Note** $\varepsilon^{1/4}$ is the real power of the nonnegative energy.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - reading: ‖Λ − Λ'‖_F² = O(ε^{1/4}) and ‖P − P'‖_Λ = O(ε^{1/4}) → one explicit constant ∃ K > 0 quantified before every other object (dimension, operators, Λ); reason: the paper's O(·)/Ω(1) constants are absolute; this is the strongest reading
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem 5.6, p.29 (proof pp.29–40)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Theorem 5.6, p.29 (Gur–Li, STOC 2027 #515). There is a universal `K > 0` such that:
for `N ≥ 2`, PSD `P` with `0 ⪯ P ⪯ I` and PSD `Λ` with `‖Λ‖_F = 1`, if `m_Λ(P) = 1/4` and
`E_Λ(P) = ε (≥ 0)`, there are PSD `P'` with `0 ⪯ P' ⪯ I` and PSD `Λ'` with `‖Λ'‖_F = 1` such that
`E_Λ'(P') = 0`, `m_Λ'(P') = 1/4`, `‖Λ − Λ'‖_F² ≤ K ε^{1/4}` and `‖P − P'‖_Λ ≤ K ε^{1/4}`.
`Λ` need not be positive definite. -/
theorem theorem_5_6 : ∃ K : ℝ, 0 < K ∧
    ∀ (d : Type) [Fintype d] [DecidableEq d], 2 ≤ Fintype.card d →
      ∀ (P : Matrix (d × d) (d × d) ℂ), P.PosSemidef → (1 - P).PosSemidef →
      ∀ (Λ : Matrix d d ℂ), Λ.PosSemidef → frobNorm Λ = 1 → mass Λ P = 1 / 4 →
      ∃ (P' : Matrix (d × d) (d × d) ℂ) (Λ' : Matrix d d ℂ),
        P'.PosSemidef ∧ (1 - P').PosSemidef ∧ Λ'.PosSemidef ∧ frobNorm Λ' = 1 ∧
        energy Λ' P' = 0 ∧ mass Λ' P' = 1 / 4 ∧
        frobNorm (Λ - Λ') ^ 2 ≤ K * energy Λ P ^ ((1 : ℝ) / 4) ∧
        lamNorm Λ (P - P') ≤ K * energy Λ P ^ ((1 : ℝ) / 4) := by sorry

end QuantumCycleColoring.FourColor
