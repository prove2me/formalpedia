-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_effect_offdiagonal_largest_eigenvalue
-- name    : QAlgorithms.Papers.Independent.Information100.P38.effect_offdiagonal_largest_eigenvalue
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:07:14.349787+00:00
-- url     : https://prove2.me/theorems/4a81f38d-ced7-4986-abd1-42cfe5f1efe4
-- title:
--   Lemma 1 / Appendix A
-- statement:
--   Fix an orthonormal reference basis of $\mathbb C^d$, $d\ge1$, and let $\Delta$ denote complete dephasing in that basis. Every effect $A$, meaning $A\ge0$ and $I-A\ge0$, satisfies
--
--   $$\lambda_{\max}(A-\Delta A)\le1-\frac1d.$$
--
--   The bound concerns the largest eigenvalue, rather than an operator norm or the smallest eigenvalue. It requires no Hamiltonian or energy-gap assumption and supplies the spectral estimate used in the robustness bound.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 7, Lemma 1 / Appendix A

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.7, Lemma 1, proved in Appendix A pp.11–12: largest off-diagonal eigenvalue
of an effect; no Hamiltonian hypotheses enter this statement. -/
theorem effect_offdiagonal_largest_eigenvalue {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsEffect A) :
    largestEnergyEigenvalue (A - energyDephasing A) ≤ 1 - 1 / (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
