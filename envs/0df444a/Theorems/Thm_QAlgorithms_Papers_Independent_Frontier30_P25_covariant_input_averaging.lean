-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_covariant_input_averaging
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.covariant_input_averaging
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:41:46.457493+00:00
-- url     : https://prove2.me/theorems/0bbc5082-bb50-491f-aa85-ea925bcd09f1
-- title:
--   Covariance averaging increases three entanglement quantities
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional CPTP map covariant under unitary representations $U,V$ of a finite group $G$, in the sense of equation (2.11). No one-design condition is required. For a density operator $\rho_A$, set $\bar\rho=|G|^{-1}\sum_g U_g\rho U_g^\dagger$. Choose normalized purifications $\psi_{RA}$ and $\varphi_{RA}$ of $\rho$ and $\bar\rho$, with $R$ isomorphic to $A$, and define $\tau=(\mathrm{id}_R\otimes\mathcal N)(\psi)$ and $\bar\tau=(\mathrm{id}_R\otimes\mathcal N)(\varphi)$.
--
--   For $\alpha>1$ and $0<\varepsilon<1$,
--
--   $$E_R(\bar\tau)\ge E_R(\tau),\qquad E_R^\varepsilon(\bar\tau)\ge E_R^\varepsilon(\tau),\qquad \widetilde E_{R,\alpha}(\bar\tau)\ge\widetilde E_{R,\alpha}(\tau).$$
--
--   Each quantity minimizes its respective relative entropy over all separable states on $R:B$: Umegaki, hypothesis-testing, or sandwiched Rényi relative entropy, with base-two logarithms and support-failure infinity. The outputs are constructed from the stated inputs. These inequalities justify symmetry reduction of the input optimization.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 23, Proposition 14

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.23, Proposition 14: group-averaged inputs increase all three REE quantities.
Both normalized purifications and both channel outputs are tied to the given input.
Only (2.11) is assumed, without the extra one-design condition. -/
theorem covariant_input_averaging
    {G A B : Type} [Fintype G] [Group G] [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (U : G →* Matrix.unitaryGroup A ℂ) (V : G →* Matrix.unitaryGroup B ℂ)
    (hcov : Covariant N U V) (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (psi phi : EuclideanSpace ℂ (A × A)) (hpsi : IsState psi) (hphi : IsState phi)
    (hpur : traceLeft (pureDensity psi) = rho)
    (havgpur : traceLeft (pureDensity phi) = groupAverage U rho)
    (alpha eps : ℝ) (halpha : 1 < alpha) (heps0 : 0 < eps) (heps1 : eps < 1) :
    let out := idTensorSuperop (R := A) N (pureDensity psi)
    let avgOut := idTensorSuperop (R := A) N (pureDensity phi)
    entanglement relativeD out ≤ entanglement relativeD avgOut ∧
    entanglement (testingD eps) out ≤ entanglement (testingD eps) avgOut ∧
    entanglement (sandwichedD alpha) out ≤ entanglement (sandwichedD alpha) avgOut := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
