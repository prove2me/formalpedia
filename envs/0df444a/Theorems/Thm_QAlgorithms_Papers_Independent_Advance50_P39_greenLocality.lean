-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_greenLocality
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.greenLocality
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:59:37.754399+00:00
-- url     : https://prove2.me/theorems/621ecd1a-ecae-46e9-bbef-128e0b46d0cf
-- title:
--   No population output implies zero Green-function contribution
-- statement:
--   Let $\mathcal M=\mathcal A+\mathcal R$ be the finite transport model with $N\ge1$, $\hbar>0$, $\Gamma>0$, nonnegative site trapping rates, Hermitian coherent evolution and trace-preserving Lindblad phonon dynamics. Let $\rho_0$ be a positive semidefinite trace-one initial matrix. Here $\mathcal A X=-\{\hbar\Gamma I+H_{\rm trap},X\}/\hbar$ and $H_{\rm trap}=\hbar\operatorname{diag}(\kappa_m)$. Let $\mathcal B$ be a complex-linear process with no site-population output: $(\mathcal B X)_{mm}=0$ for every matrix $X$ and every site $m$. Then its Eq. (9) contribution is
--   $$
--   -\frac2\hbar\operatorname{Tr}\!\left(H_{\rm recomb}\mathcal A^{-1}\mathcal B\mathcal M^{-1}\rho_0\right)=0,
--   \qquad H_{\rm recomb}=\hbar\Gamma I.
--   $$
--   This identifies a structural locality limitation of the Green-function measure. It does not imply that all energy-basis dephasing processes have zero contribution, since those can change site populations.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §V: Green-function contribution vanishes for processes without a population output

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, §V: processes with no site-population output contribute zero to (9).
This does not assert zero for all energy-basis dephasing terms. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem greenLocality {n : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (B : Superoperator n) (hpopulation : ∀ X i, (B X) i i = 0) :
    greenContribution D B rho0 = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
