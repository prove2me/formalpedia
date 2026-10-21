-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_window_change_unitary
-- name    : QAlgorithms.Papers.Independent.Next46.P20.window_change_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:18:25.232546+00:00
-- url     : https://prove2.me/theorems/905d77b6-4ad3-4ef9-a353-1142d3f11087
-- title:
--   Explicit unitary change of normalized window
-- statement:
--   Let $n\ge1$ and let $\chi_1,\chi_2\in L^2(\mathbb R^n)$ be unit windows. With $T_j\psi=\psi\otimes\overline{\chi_j}$ and $\mathcal H_j=\operatorname{Ran}T_j$, the map
--   $$
--   T_1T_2^*:\mathcal H_2\longrightarrow\mathcal H_1
--   $$
--   is a unitary bijection. Its inverse is $T_2T_1^*$.
--
--   Thus the window-dependent formulations are equivalent by the explicit transformation in the source.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 8, Remark 2.6: equivalence of window choices

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.8, Remark 2.6: the explicit change of window is T_chi1 T_chi2^*;
its inverse is the reversed composition. -/
theorem window_change_unitary {n : ℕ} (hn : 0 < n)
    (chi1 chi2 : ConfigurationL2 n) (hchi1 : ‖chi1‖ = 1) (hchi2 : ‖chi2‖ = 1) :
    ∃ E : windowSpace chi2 ≃ₗᵢ[ℂ] windowSpace chi1,
      (∀ Psi : windowSpace chi2,
        (E Psi : PhaseL2 n) = tensorEmbedding chi1 ((tensorEmbedding chi2).adjoint Psi)) ∧
      (∀ Phi : windowSpace chi1,
        (E.symm Phi : PhaseL2 n) = tensorEmbedding chi2 ((tensorEmbedding chi1).adjoint Phi)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
