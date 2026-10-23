-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_xy_spectral_equivalence
-- name    : QAlgorithms.Papers.Independent.Information100.P47.xy_spectral_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:35:09.429782+00:00
-- url     : https://prove2.me/theorems/78e69c79-4e27-4e2a-bf0e-adec0e73e775
-- title:
--   Joint X–Y POVM realizes spectral equivalence
-- statement:
--   On a qubit, let $\sigma_x,\sigma_y$ be the Pauli matrices and define the four-outcome POVM
--
--   $$M_{ij}=\frac14\left[I+\frac{(-1)^i\sigma_x+(-1)^j\sigma_y}{\sqrt2}\right],\qquad i,j\in\{0,1\}.$$
--
--   For $D_\infty(A,B)=\frac12\sum_x\|A_x-B_x\|_{\mathrm{op}}$, define coherence by minimum distance to complete POVMs diagonal in the computational basis, maximal coherence by maximizing over all unitary basis changes, and sharpness by minimum distance to $(q_x I)_x$ over probability distributions $q$. Then
--
--   $$C_{D_\infty}^{\max}(M_{XY})=S_{D_\infty}(M_{XY}).$$
--
--   This is the common-MUB endpoint of the paper's qubit example; it asserts no interpolation curve or numerical resource value.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 7, §IV A; Figure 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF pp.7–8, §IV A: the X–Y endpoint follows from Corollary 3.
The Figure 1 caption's reference to Theorem 2 is inapplicable to these noncommuting effects. -/
theorem xy_spectral_equivalence :
    maxCoherence spectralDistance xyPOVM = sharpness spectralDistance xyPOVM := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
