-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_4_7
-- name    : QuantumCycleColoring.FourColor.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:59:58.862141+00:00
-- url     : https://prove2.me/theorems/87724c61-2027-4b97-887f-8504a70bbc05
-- title:
--   Lemma 4.7: mass and energy as measurement probabilities
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and $\Lambda$ a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$. Define the bipartite state $|\Psi\rangle=\mathrm{vec}(\bar\Lambda)$ and its reduced density matrices $\rho=\mathrm{Tr}_{\mathcal A}(|\Psi\rangle\langle\Psi|)$, $\bar\rho=\mathrm{Tr}_{\mathcal B}(|\Psi\rangle\langle\Psi|)$. Then
--   $$m_\Lambda(P)=\mathrm{Tr}\big[P(\rho\otimes\bar\rho)\big],\qquad \mathcal E_\Lambda(P)=\mathrm{Tr}\big[(P\otimes P)(\rho\otimes|\Psi\rangle\langle\Psi|\otimes\bar\rho)\big].$$
--
--   So the mass is the probability of the outcome $P$ at one node, and the energy the probability of outcome $P$ at two adjacent nodes, when nodes share copies of $|\Psi\rangle$ along a line.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: ρ ⊗ |Ψ⟩⟨Ψ| ⊗ ρ̄ on four registers, with P ⊗ P acting on the first two and the last two → the Kronecker product (ρ ⊗ₖ |Ψ⟩⟨Ψ|) ⊗ₖ ρ̄, indexed by (d × (d × d)) × d, reindexed by ((a,(b,c)),d) ↦ ((a,b),(c,d)) to match P ⊗ₖ P; reason: explicit associativity of the tensor product; the same operator
--   - encoding: equalities of the (real) numbers m_Λ(P), E_Λ(P) with traces → equalities in ℂ between the real numbers mass Λ P, energy Λ P (cast to ℂ) and the traces; reason: the paper's mass and energy are these traces; the cast states the same equality
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 4.7, p.23

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 4.7, p.23 (Gur–Li, STOC 2027 #515). For PSD `P` with `0 ⪯ P ⪯ I` and PSD `Λ`
with `‖Λ‖_F = 1`, let `|Ψ⟩ = vec(Λ̄)`, `ρ = Tr_𝒜 |Ψ⟩⟨Ψ|`, `ρ̄ = Tr_ℬ |Ψ⟩⟨Ψ|`. Then
`m_Λ(P) = Tr[P (ρ ⊗ ρ̄)]` and `E_Λ(P) = Tr[(P ⊗ P)(ρ ⊗ |Ψ⟩⟨Ψ| ⊗ ρ̄)]`, the four registers of
`ρ ⊗ |Ψ⟩⟨Ψ| ⊗ ρ̄` regrouped into the two pairs on which the two copies of `P` act. -/
theorem lemma_4_7 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hPI : (1 - P).PosSemidef)
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛF : frobNorm Λ = 1) :
    let Ψ : d × d → ℂ := vecM (conjM Λ)
    let ρ : Matrix d d ℂ := ptraceA (ketBra Ψ)
    let ρbar : Matrix d d ℂ := ptraceB (ketBra Ψ)
    ((mass Λ P : ℂ) = Matrix.trace (P * (ρ ⊗ₖ ρbar))) ∧
    ((energy Λ P : ℂ) = Matrix.trace ((P ⊗ₖ P) *
      Matrix.reindex (regAssoc d) (regAssoc d) ((ρ ⊗ₖ ketBra Ψ) ⊗ₖ ρbar))) := by sorry

end QuantumCycleColoring.FourColor
