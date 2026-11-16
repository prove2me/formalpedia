-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_Supplement_lemma_B_2
-- name    : QuantumCycleColoring.FourColor.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:28.591089+00:00
-- url     : https://prove2.me/theorems/05137967-b348-43d4-ad23-77c10f524dfa
-- title:
--   Lemma B.2: $\Lambda$-mass $m\ge1/3$ forces $\Lambda$-energy $\ge m(3m-1)/2$
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and let $\Lambda\in\mathbb C^{N\times N}$ be PSD with $\|\Lambda\|_F=1$. Write $m_\Lambda(P)=\mathrm{Tr}(P(\Lambda^2\otimes\bar\Lambda^2))$ for the **$\Lambda$-mass** and $\mathcal E_\Lambda(P)=\mathrm{Tr}(\Lambda A\Lambda B)$ for the **$\Lambda$-energy**, with $A=\mathrm{Tr}_{\mathcal A}((\Lambda^2\otimes I)P)^\top$, $B=\mathrm{Tr}_{\mathcal B}((I\otimes\bar\Lambda^2)P)$; $\bar\Lambda$ is the entrywise conjugate. If $m:=m_\Lambda(P)\ge1/3$, then
--   $$\mathcal E_\Lambda(P)\ \ge\ \frac{m(3m-1)}{2}.$$
--
--   The bound is positive whenever $m>1/3$. It gives the two-colour constant $1/8$ of Theorem B.1 and the branch $m>1/2$ of its three-colour case.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: P PSD with 0 ⪯ P ⪯ I → P positive semidefinite and 1 − P positive semidefinite; reason: the definition of the Loewner order; the same instances
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma B.2, p.54 (proof pp.54–55)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor.Supplement

open QuantumCycleColoring.FourColor Matrix

/-- Lemma B.2, p.54 (Gur–Li, STOC 2027 #515). For PSD `P` on `ℂ^N ⊗ ℂ^N` with `0 ⪯ P ⪯ I` and
PSD `Λ` with `‖Λ‖_F = 1`, if `m := m_Λ(P) ≥ 1/3` then `E_Λ(P) ≥ m(3m − 1)/2`. -/
theorem lemma_B_2 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hPI : (1 - P).PosSemidef)
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛF : frobNorm Λ = 1)
    (hm : 1 / 3 ≤ mass Λ P) :
    mass Λ P * (3 * mass Λ P - 1) / 2 ≤ energy Λ P := by sorry

end QuantumCycleColoring.FourColor.Supplement
