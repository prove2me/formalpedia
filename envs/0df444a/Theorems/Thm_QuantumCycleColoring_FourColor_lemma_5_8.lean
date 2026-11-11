-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_5_8
-- name    : QuantumCycleColoring.FourColor.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:04.03051+00:00
-- url     : https://prove2.me/theorems/bb1338f7-b799-4118-b0e4-8660138e69e6
-- title:
--   Lemma 5.8: the threshold subspace $U$ is approximately $\Lambda$-invariant
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $N\ge2$, let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and let $\Lambda$ be a PSD $N\times N$ matrix with $\|\Lambda\|_F=1$, such that $m_\Lambda(P)=\tfrac14$ and $\mathcal E_\Lambda(P)=\varepsilon>0$. Let $B=\mathrm{Tr}_{\mathcal B}\big((I\otimes\bar\Lambda^2)P\big)$ with spectral decomposition $B=\sum_i\rho_iv_iv_i^\dagger$, let $U=\mathrm{span}\{v_i:\rho_i\ge\sqrt\varepsilon\}$, and let $Q=\Pi_U$, $R=\Pi_{U^\perp}$. Then the non-invariance measure satisfies
--   $$\delta:=\|Q\Lambda R\|_F^2\le K\sqrt{\varepsilon}.$$
--
--   The lemma shows that the subspace built from the large eigenvalues of $B$ is nearly preserved by $\Lambda$, which is what makes the block-diagonal approximation $\Lambda'$ of Theorem 5.6 close to $\Lambda$.
--
--   Differences from the source:
--   - encoding: Λ-mass m_Λ(P) = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: U := span{v_i : ρ_i ≥ √ε} for an eigen-decomposition of B (§5.2.1) → U := specSubspaceGe B √ε, the sum of the eigenspaces of B for real eigenvalues ≥ √ε; reason: for the Hermitian B this is the span of the eigenvectors with ρ_i ≥ √ε, independent of the chosen eigenbasis; {0} when no eigenvalue qualifies
--   - encoding: the setting of §5.2.1: P, Λ as in Theorem 5.6 (N ≥ 2, 0 ⪯ P ⪯ I, Λ PSD, ‖Λ‖_F = 1, m_Λ(P) = 1/4) with E_Λ(P) = ε > 0 → these hypotheses stated explicitly, ε being energy Λ P; reason: the lemma's sentence relies on the section's setting
--   - reading: δ = O(√ε) → one explicit constant ∃ K > 0 quantified before every other object (dimension, operators, Λ); reason: the paper's O(·)/Ω(1) constants are absolute; this is the strongest reading
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 5.8, p.30, in the setting of Theorem 5.6 and §5.2.1 (p.29)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor

open Matrix

/-- Lemma 5.8, p.30 (Gur–Li, STOC 2027 #515), in the setting of §5.2.1 (p.29): `N ≥ 2`,
`P` PSD with `0 ⪯ P ⪯ I`, `Λ` PSD with `‖Λ‖_F = 1`, `m_Λ(P) = 1/4` and `E_Λ(P) = ε > 0`;
`B = Tr_ℬ((I ⊗ Λ̄²) P)`, `U` the span of the eigenvectors of `B` with eigenvalue `≥ √ε`,
`Q = Π_U`, `R = Π_{U^⊥}`. Then `δ = ‖Q Λ R‖_F² = O(√ε)`: one universal `K > 0` with
`δ ≤ K √ε`. -/
theorem lemma_5_8 : ∃ K : ℝ, 0 < K ∧
    ∀ (d : Type) [Fintype d] [DecidableEq d], 2 ≤ Fintype.card d →
      ∀ (P : Matrix (d × d) (d × d) ℂ), P.PosSemidef → (1 - P).PosSemidef →
      ∀ (Λ : Matrix d d ℂ), Λ.PosSemidef → frobNorm Λ = 1 →
      mass Λ P = 1 / 4 → 0 < energy Λ P →
      let U := specSubspaceGe (energyB Λ P) (Real.sqrt (energy Λ P))
      frobNorm (projMat U * Λ * projMat Uᗮ) ^ 2 ≤ K * Real.sqrt (energy Λ P) := by sorry

end QuantumCycleColoring.FourColor
