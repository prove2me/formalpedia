-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_fact_4_8
-- name    : QuantumCycleColoring.FourColor.fact_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:14.816261+00:00
-- url     : https://prove2.me/theorems/664f3d2c-c654-4606-b156-a8e0e3f6a483
-- title:
--   Fact 4.8: the $\Lambda$-energy is monotone in the PSD order
-- statement:
--   Let $P,Q$ be PSD operators on $\mathbb C^N\otimes\mathbb C^N$ and $\Lambda$ a PSD $N\times N$ matrix. If $P\preceq Q$ (that is, $Q-P$ is PSD), then
--   $$\mathcal E_\Lambda(P)\le\mathcal E_\Lambda(Q).$$
--
--   Monotonicity lets energy bounds pass from an operator to anything above or below it in the PSD order.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Fact 4.8, p.24

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Fact 4.8, p.24 (Gur–Li, STOC 2027 #515). For PSD `P, Q` on `ℂ^d ⊗ ℂ^d` and PSD `Λ`,
if `P ⪯ Q` then `E_Λ(P) ≤ E_Λ(Q)`. -/
theorem fact_4_8 {d : Type} [Fintype d] [DecidableEq d]
    (P Q : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hPQ : (Q - P).PosSemidef) :
    energy Λ P ≤ energy Λ Q := by sorry

end QuantumCycleColoring.FourColor
