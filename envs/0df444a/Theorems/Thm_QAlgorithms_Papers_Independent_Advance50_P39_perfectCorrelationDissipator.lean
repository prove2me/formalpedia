-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_perfectCorrelationDissipator
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.perfectCorrelationDissipator
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:01:12.769026+00:00
-- url     : https://prove2.me/theorems/6062979c-f04c-4d9f-8a88-a1f8eaae65a9
-- title:
--   Perfect common-site correlations annihilate the phonon dissipator
-- statement:
--   Let $N\ge1$, $\hbar>0$, and let $U_{mM}=c_m(M)$ be a unitary change between complete site and exciton bases, with real exciton energies $E_M$, allowing degeneracy. Define the site-projector transition matrices in exciton coordinates by $(A_m(\omega))_{MN}=\overline{U_{mM}}U_{mN}$ when $E_M-E_N=\hbar\omega$, and zero otherwise. Let $g(\omega)\ge0$ be the common scalar rate prefactor. At the exactly perfectly correlated endpoint $C_{mn}=1$,
--   $$
--   \sum_m A_m(\omega)=\begin{cases}I,&\omega=0,\\0,&\omega\ne0,\end{cases}
--   \qquad
--   \mathcal L_\omega(X)=0,\qquad \sum_\omega\mathcal L_\omega(X)=0
--   $$
--   for every matrix $X$, where $\mathcal L_\omega(X)=g(\omega)\sum_{m,n}[A_mXA_n^\dagger-\{A_mA_n^\dagger,X\}/2]$ is the literal printed Eq. (5) frequency term and the final sum is over all Bohr frequencies. This endpoint conclusion survives the printed loss-order defect and covers relaxation and dephasing. It makes no claim that the Lamb shift vanishes or that a finite large correlation radius has exactly zero dissipation.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §IV: perfectly correlated phonon noise has zero relaxation/dephasing dissipator

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,5, §IV: exactly C_mn=1 gives zero relaxation/dephasing. The combined
jump is I at zero frequency and zero otherwise. This holds even for the printed
loss order; it says nothing about the non-scalar Lamb shift or finite large radius. -/
theorem perfectCorrelationDissipator {n : ℕ} (D : ExcitonData n) (g : ℝ → ℝ)
    (hrates : ∀ omega, 0 ≤ g omega) :
    (∀ omega, ∑ m, siteTransition D m omega =
      if omega = 0 then (1 : SiteMatrix n) else 0) ∧
    (∀ omega X, printedPhononAt D (fun _ _ => 1) g omega X = 0) ∧
    (∀ X, printedPhonon D (fun _ _ => 1) g X = 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
