-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_4_2
-- name    : QuantumCycleColoring.FourColor.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:59:57.148937+00:00
-- url     : https://prove2.me/theorems/cd6057de-2e91-42d0-b6ed-a4e3bb554913
-- title:
--   Lemma 4.2: spectral formula for the $\Lambda$-energy
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ and $\Lambda$ a PSD $N\times N$ matrix.
--
--   1. For every finite family of matrices $\{M_k\}_k\subseteq\mathbb C^{N\times N}$ with $P=\sum_k\mathrm{vec}(M_k)\mathrm{vec}(M_k)^\dagger$,
--   $$\mathcal E_\Lambda(P)=\sum_{k,\ell}\|\Lambda M_k\Lambda M_\ell\Lambda\|_F^2 .$$
--   2. Such a family always exists.
--
--   The formula expresses the energy through the multiplicative structure of the matrix space spanned by the $M_k$; it is the basic tool for computing and bounding energies.
--
--   **Formalization Note** The paper adds that a family can be obtained from a spectral decomposition of $P$; that remark describes how to find one and is covered by the existence clause.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: any finite family {M_k}_k → a family M : Fin K → Matrix d d ℂ for some K : ℕ; reason: a finite family is indexed by Fin K after enumeration; the same families
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 4.2, p.21

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 4.2, p.21 (Gur–Li, STOC 2027 #515). For PSD `P` on `ℂ^d ⊗ ℂ^d` and PSD `Λ`:
(1) for every finite family `M_k` with `P = ∑_k vec(M_k) vec(M_k)†`,
`E_Λ(P) = ∑_{k,ℓ} ‖Λ M_k Λ M_ℓ Λ‖_F²`; (2) such a family always exists. -/
theorem lemma_4_2 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef)
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) :
    (∀ (K : ℕ) (M : Fin K → Matrix d d ℂ), P = ∑ k, ketBra (vecM (M k)) →
      energy Λ P = ∑ k, ∑ l, frobNorm (Λ * M k * Λ * M l * Λ) ^ 2) ∧
    (∃ (K : ℕ) (M : Fin K → Matrix d d ℂ), P = ∑ k, ketBra (vecM (M k))) := by sorry

end QuantumCycleColoring.FourColor
