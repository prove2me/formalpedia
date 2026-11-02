-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_gelfand_stone_canonical_homeomorphism
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.gelfand_stone_canonical_homeomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:48:48.980445+00:00
-- url     : https://prove2.me/theorems/eb2b6858-3687-423c-8aab-d4b30d653653
-- title:
--   Theorem 3.2
-- statement:
--   Let $\mathcal A$ be a unital abelian von Neumann algebra on an arbitrary complex Hilbert space. Its Gelfand spectrum, consisting of nonzero continuous multiplicative linear functionals with the weak dual topology, is canonically homeomorphic to its projection-lattice Stone spectrum:
--
--   $$\Omega(\mathcal A)\xrightarrow{\ \cong\ }Q(\mathcal A),\qquad
--   \tau\longmapsto\{P\in P(\mathcal A):\tau(P)=1\}.$$
--
--   For a quasipoint $\mathfrak B$, the inverse character takes value $1$ on its projections and $0$ on the others. On finite spectral sums its value is $\sum_j c_j\mathbf1_{\mathfrak B}(P_j)$; it is a continuous character on the entire algebra. No normality of characters, finite dimensionality or separability is asserted.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 61, Theorem 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Theorem 3.2; de Groote, Observables I, PDF p./pp. 61, 62.
-/
theorem gelfand_stone_canonical_homeomorphism {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : VonNeumannAlgebra H)
    (hcomm : ∀ a b : R.toStarSubalgebra, a * b = b * a) :
    ∃ h : WeakDual.characterSpace ℂ R.toStarSubalgebra ≃ₜ StoneSpectrum (Projection R),
      (∀ chi, (h chi).val = {p | chi ⟨p.val, p.prop.1⟩ = 1}) ∧
      (∀ B (p : Projection R), (h.symm B) ⟨p.val, p.prop.1⟩ =
        @ite ℂ (p ∈ B.val) (Classical.propDecidable _) 1 0) ∧
      (∀ B (n : ℕ) (c : Fin n → ℂ) (p : Fin n → Projection R),
        (h.symm B) (∑ i, c i • (⟨(p i).val, (p i).prop.1⟩ : R.toStarSubalgebra)) = spectralSumFunction c p B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
