-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_4_9
-- name    : QuantumCycleColoring.FourColor.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:16.790193+00:00
-- url     : https://prove2.me/theorems/95184ac7-9d2c-41a6-92e0-984942fe0060
-- title:
--   Lemma 4.9: the $\Lambda$-energy is $6$-Lipschitz in $\Lambda$
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and let $\Lambda,\Lambda'$ be PSD $N\times N$ matrices with $\|\Lambda\|_F=\|\Lambda'\|_F=1$. Then
--   $$|\mathcal E_\Lambda(P)-\mathcal E_{\Lambda'}(P)|\le 6\,\|\Lambda-\Lambda'\|_F .$$
--
--   This continuity in the weight matrix is what allows the stability theorem to move from $\Lambda$ to a nearby $\Lambda'$ at small cost in energy.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 4.9, p.25 (proof in Appendix A.2, pp.52–53)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 4.9, p.25 (Gur–Li, STOC 2027 #515). For PSD `P` with `0 ⪯ P ⪯ I` and PSD
`Λ, Λ'` with `‖Λ‖_F = ‖Λ'‖_F = 1`, `|E_Λ(P) − E_Λ'(P)| ≤ 6 ‖Λ − Λ'‖_F`. -/
theorem lemma_4_9 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hPI : (1 - P).PosSemidef)
    (Λ Λ' : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛ' : Λ'.PosSemidef)
    (hΛF : frobNorm Λ = 1) (hΛF' : frobNorm Λ' = 1) :
    |energy Λ P - energy Λ' P| ≤ 6 * frobNorm (Λ - Λ') := by sorry

end QuantumCycleColoring.FourColor
