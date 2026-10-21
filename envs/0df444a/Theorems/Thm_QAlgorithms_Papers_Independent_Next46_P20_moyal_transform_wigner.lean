-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_moyal_transform_wigner
-- name    : QAlgorithms.Papers.Independent.Next46.P20.moyal_transform_wigner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:26:01.358133+00:00
-- url     : https://prove2.me/theorems/b92badb1-cd35-4ea4-81fb-f9a3bc515433
-- title:
--   General unitary shear formula and normalized cross-Wigner transform
-- statement:
--   Let $n\ge1$ and define $U=U_D(-\log\sqrt2)U_R(-\pi/4)$. This operator is unitary on phase-space $L^2$ and obeys
--   $$
--   U\Psi=\mathcal F_p^{-1}\big[(\mathcal F_p\Psi)(x-\xi_p/2,x+\xi_p/2)\big].
--   $$
--   For a unit window $\chi\in L^2(\mathbb R^n)$, set $\widehat\chi=\mathcal F\chi$. For every $\psi\in L^2(\mathbb R^n)$,
--   $$
--   U(\psi\otimes\overline{\widehat\chi})(x,p)
--   =(2\pi)^{-n/2}\int e^{ip\cdot y}\psi(x-y/2)\overline{\chi(x+y/2)}\,dy.
--   $$
--   The right side represents the normalized Wigner map $\mathcal W(\psi,\chi)=(2\pi)^{n/2}W(\psi,\chi)$, where $W$ is the conventional cross-Wigner distribution. Both formulas are understood in $L^2$, with representative formulas almost everywhere.
--
--   This retains both conclusions and makes the source's explicitly mentioned normalization factor visible.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 21, Corollary 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.21–22, Corollary 5.4: BOTH the general partial-Fourier shear formula
and the separated tensor identity, with the explicit normalized Wigner factor.
All equalities of L2 representatives are a.e. -/
theorem moyal_transform_wigner {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    unitaryL2 (moyalTransform (n := n)) ∧
    RealizesConfigurationFourier (configurationFourier (n := n)) ∧
    RealizesL2Formula (fun f z => f (mixedShear z)) (coordinatePullback (mixedShear (n := n))) ∧
    moyalTransform (n := n) = partialFourier.adjoint.comp
      ((coordinatePullback mixedShear).comp partialFourier) ∧
    (∀ psi : ConfigurationL2 n,
      moyalTransform (tensorEmbedding (configurationFourier chi) psi) = normalizedWigner psi chi ∧
      (∀ᵐ z : PhaseCoordinates n, normalizedWigner psi chi z = wignerFormula psi chi z)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
