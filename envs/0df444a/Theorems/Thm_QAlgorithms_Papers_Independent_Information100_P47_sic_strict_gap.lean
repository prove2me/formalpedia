-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_sic_strict_gap
-- name    : QAlgorithms.Papers.Independent.Information100.P47.sic_strict_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:35:56.727295+00:00
-- url     : https://prove2.me/theorems/690a3ee8-24ed-4149-b6f1-e0ea243f79f4
-- title:
--   Strict spectral coherence–sharpness gap for a tetrahedral SIC
-- statement:
--   Let $r_1,\ldots,r_4\in\mathbb R^3$ be the vertices of any regular tetrahedron on the unit Bloch sphere: $\|r_x\|_2=1$ and $r_x\cdot r_y=-1/3$ for $x\ne y$. With the Pauli vector $\boldsymbol\sigma=(\sigma_x,\sigma_y,\sigma_z)$, form the tetrahedral SIC POVM $M_x=(I+r_x\cdot\boldsymbol\sigma)/4$. Use the spectral distance $D_\infty(A,B)=\frac12\sum_x\|A_x-B_x\|_{\mathrm{op}}$. Define $C_{D_\infty}^{\max}$ by minimum distance to complete diagonal POVMs followed by maximum over all unitary basis changes, and define $S_{D_\infty}$ by minimum distance to trivial POVMs $(q_xI)_x$ for probability distributions $q$. Then
--
--   $$C_{D_\infty}^{\max}(M)<S_{D_\infty}(M).$$
--
--   The strict endpoint gap is independent of the tetrahedron's orientation and outcome labeling. No exact size of the gap is asserted.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 7, §IV A; Figure 1 at q=0

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF pp.7–8, §IV A and Figure 1 at q=0: a strict gap for any labeled tetrahedral SIC.
The source supplies no exact numerical gap. -/
theorem sic_strict_gap (r : Fin 4 → Fin 3 → ℝ) (hr : IsTetrahedron r) :
    maxCoherence spectralDistance (sicPOVM r) < sharpness spectralDistance (sicPOVM r) := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
