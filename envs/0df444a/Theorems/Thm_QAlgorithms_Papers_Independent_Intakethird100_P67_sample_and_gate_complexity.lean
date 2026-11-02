-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_sample_and_gate_complexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.sample_and_gate_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:50:42.814193+00:00
-- url     : https://prove2.me/theorems/83f9234a-c0d1-421f-8ee4-be38c75dddaf
-- title:
--   Universal Quantum Emulator: sample and gate complexity, Eqs.(28)–(29)
-- statement:
--   Let $D=2^n$ and let the normalized pure samples $\{\phi_k\}_{k=1}^K$, $K\ge2$, generate the full matrix algebra on their span $H_{\rm in}$, of dimension $d$. Fix an anchor sample. Write $\lambda_\perp$ for the operator norm of the vectorized compressed reflection channel. There is a single family of circuits, independent of the unknown samples, unitary $U$, and new input, that uses only supplied input/output density copies, single-qubit gates and controlled-controlled-SWAP gates. For every $0<\epsilon<1$, its parameters can be chosen using $d$, $\lambda_\perp$ and $\epsilon$ so that, uniformly for all density operators $\rho$ supported on $H_{\rm in}$,
--
--   $$\tfrac12\|\mathcal E_U(\rho)-U\rho U^\dagger\|_1\le\epsilon,\qquad N_{\rm tot}\le C\frac{d^2}{\epsilon(1-\lambda_\perp)^2}L^p,\qquad t_{\rm tot}\le C\frac{d^2n}{\epsilon(1-\lambda_\perp)^2}L^p,$$
--
--   where $L=1+\log(d+1)+\log(1+\epsilon^{-1})$, and $C>0$ and the integer $p\ge0$ are absolute. Counts are actual supplied-copy registers and elementary gate-list lengths. The number of erasure rounds is zero for $d=1$, and otherwise at least one and the ceiling of $\log(8\epsilon^{-2}(d-1))/(1-\lambda_\perp)$. The density-matrix-exponentiation precision uses an absolute multiple of $(4T+1)/\epsilon$ copies per reflection. This records the gap-dependent content of Eqs.(28)–(29), without a dimension-only convergence promise.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 7, Universal Quantum Emulator: sample and gate complexity, Eqs.(28)–(29)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.7,19, Eqs.(28)–(29): a sample-only circuit family is fixed before every
unknown sample, target unitary, and new input. Copy counts are resource registers and gate
counts are elementary list lengths. d=1 uses exact reset. For d>=2 the sample-dependent
gap remains explicit. Single-qubit and systemControlled-systemControlled-SWAP gates are counted, with
D=2^n. B19's printed error allocation is corrected by fixed-factor rescaling. -/
theorem sample_and_gate_complexity :
    ∃ (C c : ℝ) (power : ℕ) (F : EmulatorFamily), 0 < C ∧ 0 < c ∧
    ∀ (n k : ℕ), 2 ≤ k → ∀ (a : Fin k) (phi : Fin k → EuclideanSpace ℂ (Qubits n)),
      (∀ j, IsState (phi j)) → Generates (pureSamples phi) →
      ∀ eps : ℝ, 0 < eps → eps < 1 →
      let d := sampleDimension (pureSamples phi)
      let lam := lambdaPerp phi a
      let T := precisionRounds d lam eps
      let m := max 1 ⌈c * (4*T+1) / eps⌉₊
      let budget := C * (d : ℝ)^2 * eps⁻¹ / (1-lam)^2 * slowFactor d eps power
      (∀ h : Fin T → Fin k, ((F n k a T m h).copies : ℝ) ≤ budget ∧
        ((F n k a T m h).gates.length : ℝ) ≤ budget * n) ∧
      (∀ (U : Matrix.unitaryGroup (Qubits n) ℂ) (rho : Matrix (Qubits n) (Qubits n) ℂ),
        IsDensityMatrix rho → InSampleSupport (pureSamples phi) rho →
        traceDistance
          (∑ h : Fin T → Fin k, (historyWeight (nonanchorProbability a) h : ℂ) •
            (F n k a T m h).output (inputOutputRecords phi (U : Matrix (Qubits n) (Qubits n) ℂ)) rho)
          (densityConjugation (U : Matrix (Qubits n) (Qubits n) ℂ) rho) ≤ eps) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
