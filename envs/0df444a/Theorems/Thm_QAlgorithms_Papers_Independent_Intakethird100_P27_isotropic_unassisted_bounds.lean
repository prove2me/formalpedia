-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_isotropic_unassisted_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.isotropic_unassisted_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:17:25.730061+00:00
-- url     : https://prove2.me/theorems/1bb66d01-5642-4e56-a725-268c9f156006
-- title:
--   Explicit assisted lower curves and convexified purification upper bound
-- statement:
--   For the memoryless maximally mixed qubit source with Bell purification $\Phi$ and distortion observable $I-\Phi$, let $R^q(D)$ be the operational unassisted quantum rate in qubits per copy. For $0\le D\le1$, define the two explicit curves from Theorems 11 and 12 by
--
--   $$L_{\rm ea}(D)=\begin{cases}1-\tfrac12H(1-D,D/3,D/3,D/3),&D\le3/4,\\0,&D>3/4,\end{cases}\qquad L_{\to}(D)=\begin{cases}h_2(1/2+\sqrt{D(1-D)}),&D<1/2,\\0,&D\ge1/2.\end{cases}$$
--
--   Here $H$ is Shannon entropy and $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$, with zero logarithmic terms contributing zero. Put $\tau_d=(1-d)\Phi+(d/3)(I-\Phi)$ and $c(d)=E_p(\tau_d)$ for $0\le d\le3/4$, and $c(d)=0$ for $3/4<d\le1$. Define
--
--   $$U(D)=\inf\left\{\sum_{i=1}^m p_i c(d_i):m\ge1,\ p_i\ge0,\ \sum_i p_i=1,\ 0\le d_i\le1,\ \sum_i p_id_i\le D\right\}.$$
--
--   Then
--
--   $$\max\{L_{\rm ea}(D),L_{\to}(D)\}\le R^q(D)\le U(D).$$
--
--   $E_p$ is optimized over all finite normalized purifications with exactly the prescribed marginal. The upper bound uses finite time-sharing mixtures, not an assumed numerical evaluation; no exact formula for the unassisted rate is claimed.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 9, §V-A, unnumbered; p.10 and footnote 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P27

open Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRB mutualInformation bipartiteBlock epr)

open QAlgorithms.Papers.Independent.Information100.P08 (formation)

open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

open QAlgorithms.Papers.Independent.Bridge50.P37 (isotropicState normalizedEntangledProjection)

/-- PDF pp.9--10, unnumbered bounds and footnote 2: the explicit curves from
Theorems 11 and 12 lower-bound the unassisted operational rate, which is at most
the convexified exact E_p strategy cost. The Devetak--Berger curve has no factor
1/2 before binary entropy and vanishes for D >= 1/2. This is not an exact formula
for the unassisted rate. -/
theorem isotropic_unassisted_bounds
    (S : DistortionSource (Fin 2) (Fin 2))
    (hsource : pureDensity S.psi = epr 2) (hdelta : S.delta = 1 - epr 2)
    (D : ℝ) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    max (ENNReal.ofReal (if D ≤ 3 / 4 then 1 - isotropicEntropy D / 2 else 0))
      (ENNReal.ofReal (if D < 1 / 2 then
        binEntropy2 (1 / 2 + Real.sqrt (D * (1 - D))) else 0)) ≤
      rateDistortion S .unassisted D ∧
    rateDistortion S .unassisted D ≤ isotropicConvexUpper D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
