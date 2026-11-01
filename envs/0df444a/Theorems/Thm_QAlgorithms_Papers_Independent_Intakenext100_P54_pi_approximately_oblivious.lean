-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_pi_approximately_oblivious
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.pi_approximately_oblivious
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:42:07.502868+00:00
-- url     : https://prove2.me/theorems/0ade7290-ff62-4446-b66e-5ad2c7a70b5b
-- title:
--   Section VI.B: protocol Pi is approximately oblivious
-- statement:
--   Let $D\ge1$ and $0<\varepsilon\le1$. Protocol $\Pi$ can be chosen with $1\le K\le(10/\varepsilon)^2D\log_2(20D/\varepsilon)$ good messages and modified by replacing its failure announcement uniformly with a good message. Denote its actual receiver output by $\rho_\psi$ and its full receiver record by $\mathcal R_\psi$, including message and pre-decoding quantum state. There is one fixed CPTP simulator
--
--   $$T(\rho)=\frac1K\sum_k|k\rangle\langle k|\otimes\overline{U_k}\rho U_k^\top$$
--
--   such that, for every normalized pure target,
--
--   $$\tfrac12\|\psi-\rho_\psi\|_1\le\varepsilon,\qquad
--   \tfrac12\|\mathcal R_\psi-T(\rho_\psi)\|_1\le\varepsilon.$$
--
--   The unitaries, code, and simulator precede the target. The simulator consumes the actual approximate output, and Alice's private failure flag is not part of the receiver record. This is approximate preparation and approximate obliviousness in Definition 20.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 13, Section VI.B: protocol Pi is approximately oblivious

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Section VI.B, PDF pp.12–13: Pi is approximate and approximately oblivious with
parameters (eps,eps). The simulator consumes the actual output, as Definition 20 requires. -/
theorem pi_approximately_oblivious (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ (K : ℝ) ≤ randomisingBound D eps ∧
      ∃ U : Fin K → Matrix.unitaryGroup (Fin D) ℂ,
        Randomising U eps ∧ IsChannel (piSimulator U) ∧ ∀ psi : RSPVector (Fin D),
          traceNorm (pureDensity psi.val - piApproxOutput U eps psi) / 2 ≤ eps ∧
          traceNorm (piRecord U eps psi - piSimulator U (piApproxOutput U eps psi)) / 2 ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
