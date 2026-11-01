-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_posttest_symmetry
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.posttest_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:55:08.509497+00:00
-- url     : https://prove2.me/theorems/67f12a86-3dde-4e84-9ccd-246fa88e03cd
-- title:
--   Symmetry after measuring the test
-- statement:
--   Let $n\ge1$ and let $U$ be any joint unitary attack on $2n$ signals with a fixed initial pure probe. Fix the bases and balanced partition and let $E^s$ be its coherent symmetrization from Eq. (13), with test positions written first. Then, for every test input $i_T$, test outcome $j_T$, and information inputs $i_I,k_I$,
--
--   $$p(j_T\mid i_T,i_I)=p(j_T\mid i_T,k_I).$$
--
--   For a positive common probability, the conditional probes $E_{i_I,j_I}$ have $\sum_{j_I}\|E_{i_I,j_I}\|^2=1$ and retain Eq. (18):
--
--   $$E_{i_I,j_I}(m_T,m_I,q)=2^{-n/2}(-1)^{(i_I\oplus j_I)\cdot m_I}F_{i_I\oplus m_I,j_I\oplus m_I}(m_T,q).$$
--
--   Here $m_T,m_I$ are the retained test and information mask registers, $q$ is the original probe coordinate, and $F$ is computed by symmetrizing only the test mask and dividing by the square root of the same common test probability. This permits the conditional Fourier analysis; individual rows of $F$ need not be normalized.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 14, Appendix C: symmetry survives test measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix C, PDF pp.14--15, Eqs.(16)--(18): the probability of a test
outcome is independent of the information input. Positive-probability conditional
probes are normalized and retain the explicitly constructed information symmetry. -/
theorem posttest_symmetry {n d : ℕ} (hn : 1 ≤ n)
    (U : Matrix.unitaryGroup (Fin d × Qubits (n + n)) ℂ) (e0 : Fin d)
    (iT jT : Qubits n) :
    (∀ iI kI, testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT iI =
      testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT kI) ∧
    (0 < testProbability (coherentBitSymmetrize (attackProbes U e0)) iT jT (fun _ => false) →
      (∀ iI, ∑ jI, ‖conditionedSymmetric U e0 iT jT iI jI‖ ^ 2 = 1) ∧
      ∀ iI jI mT mI q,
        conditionedSymmetric U e0 iT jT iI jI (Fin.append mT mI, q) =
          ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) * character (iI + jI) mI *
            testOnlyConditioned U e0 iT jT (iI + mI) (jI + mI) (mT, q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
