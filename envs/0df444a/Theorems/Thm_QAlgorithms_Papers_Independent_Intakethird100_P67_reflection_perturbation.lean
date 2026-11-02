-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_reflection_perturbation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.reflection_perturbation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:56:32.243497+00:00
-- url     : https://prove2.me/theorems/37fa9de0-535b-4cf5-a9aa-89061e388a94
-- title:
--   Appendix F, Eqs.(F1)–(F5): reflection and unitary perturbation estimates
-- statement:
--   Let two normalized pure sample families $\phi_k,\widetilde\phi_k$ satisfy $|\langle\phi_k|\widetilde\phi_k\rangle|^2\ge1-\delta^2$, $\delta\ge0$. For $R_\phi=I-2\lvert\phi\rangle\langle\phi\rvert$ and the corresponding controlled reflections and $W(k)=R(k)HR(a)$,
--
--   $$\|R_\phi-R_{\widetilde\phi}\|_\infty=2\sqrt{1-|\langle\phi|\widetilde\phi\rangle|^2},\quad\|R^c_k-\widetilde R^c_k\|_\infty\le2\delta,\quad\|W(k)-\widetilde W(k)\|_\infty\le4\delta.$$
--
--   For arbitrary pairs of unitary factors, the norm of the difference of their two-factor products is at most the sum of the two factor differences. For every density operator $\sigma$ and unitaries $V,\widetilde V$,
--
--   $$\tfrac12\|V\sigma V^\dagger-\widetilde V\sigma\widetilde V^\dagger\|_1\le\|V-\widetilde V\|_\infty.$$
--
--   The analogous distance for finite probability mixtures is at most the corresponding average of operator-norm differences. These are F1–F5, independent of how a consumed output-anchor resource is changed.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 27, Appendix F, Eqs.(F1)–(F5): reflection and unitary perturbation estimates

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.27, F1–F5: all algebraic perturbation estimates, without claiming Eq.(33)
for changed consumed-anchor resources. -/
theorem reflection_perturbation [Nonempty L] (phi phitilde : K → EuclideanSpace ℂ I) (a : K)
    (hphi : ∀ k, IsState (phi k)) (htilde : ∀ k, IsState (phitilde k))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hoverlap : ∀ k, 1 - delta ^ 2 ≤ ‖inner ℂ (phi k) (phitilde k)‖ ^ 2) :
    (∀ k, QAlgorithms.specNorm (sampleReflection (phi k) - sampleReflection (phitilde k)) =
      2 * Real.sqrt (1 - ‖inner ℂ (phi k) (phitilde k)‖ ^ 2)) ∧
    (∀ k, QAlgorithms.specNorm (systemControlled (sampleReflection (phi k)) - systemControlled (sampleReflection (phitilde k))) ≤ 2 * delta) ∧
    (∀ k, QAlgorithms.specNorm (erasureGate phi a k - erasureGate phitilde a k) ≤ 4 * delta) ∧
    (∀ V1 V2 W1 W2 : Matrix.unitaryGroup I ℂ,
      QAlgorithms.specNorm ((W2 : Matrix I I ℂ) * (W1 : Matrix I I ℂ) - (V2 : Matrix I I ℂ) * (V1 : Matrix I I ℂ)) ≤
        QAlgorithms.specNorm ((W2 : Matrix I I ℂ) - (V2 : Matrix I I ℂ)) + QAlgorithms.specNorm ((W1 : Matrix I I ℂ) - (V1 : Matrix I I ℂ))) ∧
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho → ∀ V W : Matrix.unitaryGroup I ℂ,
      traceDistance (densityConjugation (V : Matrix I I ℂ) rho) (densityConjugation (W : Matrix I I ℂ) rho) ≤
        QAlgorithms.specNorm ((V : Matrix I I ℂ) - (W : Matrix I I ℂ))) ∧
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho → ∀ p : L → ℝ, QAlgorithms.Learning.IsDistribution p →
      ∀ V W : L → Matrix.unitaryGroup I ℂ,
      traceDistance (∑ l, (p l : ℂ) • densityConjugation (V l : Matrix I I ℂ) rho)
        (∑ l, (p l : ℂ) • densityConjugation (W l : Matrix I I ℂ) rho) ≤
        ∑ l, p l * QAlgorithms.specNorm ((V l : Matrix I I ℂ) - (W l : Matrix I I ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
