-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_polynomial_phase_injection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.polynomial_phase_injection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:14:23.803983+00:00
-- url     : https://prove2.me/theorems/3afed43d-dbc0-469a-a49f-3e8abe0581fd
-- title:
--   §XI.B (124)–(127), Fig.6: phase-state gate injection
-- statement:
--   Let $\phi$ be a real polynomial. Form the joint wavefunction $\psi(q_1)e^{i\phi(q_2)}$, apply the inverse-SUM pullback $F(q_1,q_2)\mapsto F(q_1,q_2+q_1)$, and take the target-position fiber $q_2=a$. For every $L^2$ data wavefunction and every outcome parameter $a\in\mathbb R$, the inverse-SUM phase-ancilla conditional multiplier $e^{i\phi(q+a)}$ is corrected by
--
--   $$U(a,q)=e^{i[\phi(q)-\phi(q+a)]},\qquad U(a,q)e^{i\phi(q+a)}\psi(q)=e^{i\phi(q)}\psi(q).$$
--
--   If $\deg\phi\le3$, the correction phase has degree at most two and its derivative is affine; the exact momentum conjugation identity on differentiable data waves is included. For $\phi(q)=\gamma q^3$ the correction phase is $-\gamma(3aq^2+3a^2q+a^3)$. Also, for $\gamma,\gamma'>0$, $V_\gamma=S_r^{-1}V_{\gamma'}S_r$ with $r=\gamma/\gamma'$ and coordinate squeeze $q\mapsto r^{1/3}q$, retaining the wavefunction normalization.
--
--   The ideal resource is unnormalizable, and no outcome probability law is assigned to it.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 16, §XI.B (124)–(127), Fig.6: phase-state gate injection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XI.B (124)–(127), Fig.6, PDF p.16: conditional phase-state injection for every outcome.
The joint resource, inverse SUM pullback, and target-position fiber are constructed
explicitly. The ideal resource has no normalized outcome probability law. -/
theorem polynomial_phase_injection (phi : Polynomial ℝ) :
    (∀ (a : ℝ) (psi : ℝ → ℂ), MemLp psi 2 volume → ∀ q : ℝ,
      injectionPositionFiber (injectionInverseSum (injectionJointWave phi psi)) a q =
        cisPhase (phi.eval (q + a)) * psi q) ∧
    (∀ (a : ℝ) (psi : ℝ → ℂ), MemLp psi 2 volume → ∀ q : ℝ,
      phaseCorrection phi a q *
        injectionPositionFiber (injectionInverseSum (injectionJointWave phi psi)) a q =
        cisPhase (phi.eval q) * psi q) ∧
    (phi.natDegree ≤ 3 → ∀ a : ℝ, (phi - phi.comp (Polynomial.X + Polynomial.C a)).natDegree ≤ 2) ∧
    (phi.natDegree ≤ 3 → ∀ a : ℝ, ∃ A B : ℝ, ∀ q : ℝ,
      (phi - phi.comp (Polynomial.X + Polynomial.C a)).derivative.eval q = A * q + B) ∧
    (∀ a q : ℝ, ∀ psi : ℝ → ℂ, MemLp psi 2 volume → DifferentiableAt ℝ psi q →
      conj (phaseCorrection phi a q) *
        (-Complex.I * deriv (fun x => phaseCorrection phi a x * psi x) q) =
      -Complex.I * deriv psi q +
        (((phi - phi.comp (Polynomial.X + Polynomial.C a)).derivative.eval q : ℝ) : ℂ) * psi q) ∧
    (∀ gamma gammaPrime : ℝ, 0 < gamma → 0 < gammaPrime →
      ∀ psi : ℝ → ℂ, MemLp psi 2 volume →
      squeezeWave ((gamma / gammaPrime) ^ (-(1 : ℝ) / 3))
        (cubicWave gammaPrime (squeezeWave ((gamma / gammaPrime) ^ ((1 : ℝ) / 3)) psi)) =
          cubicWave gamma psi) ∧
    (∀ gamma a q : ℝ,
      phaseCorrection (Polynomial.C gamma * Polynomial.X ^ 3) a q =
        cisPhase (-gamma * (3 * a * q ^ 2 + 3 * a ^ 2 * q + a ^ 3))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
