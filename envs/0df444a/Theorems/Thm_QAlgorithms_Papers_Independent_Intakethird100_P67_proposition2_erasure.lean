-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_proposition2_erasure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.proposition2_erasure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:52:42.619895+00:00
-- url     : https://prove2.me/theorems/4c0008b7-42c1-4eb5-b210-8cee6f572838
-- title:
--   Proposition 2: convergence of coherent erasure
-- statement:
--   Let $K\ge2$ normalized pure samples generate the full algebra on their span, and fix one anchor $\phi_a$. At each round choose a nonanchor index independently and uniformly, apply $R(k)HR(a)$ to the system and a fresh $\lvert-\rangle$ ancilla, and trace out that ancilla. Let $\mathcal W$ be this averaged channel. For every supported density operator $\rho$,
--
--   $$\lim_{T\to\infty}\|\mathcal W^T(\rho)-\lvert\phi_a\rangle\langle\phi_a\rvert\|_1=0.$$
--
--   Moreover, the anchor density is the unique supported fixed density operator. The average is over histories; no claim is made about every individual random history. The displayed nonanchor average is restricted to $K\ge2$; rank-one reset is covered separately in the ideal-error result.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 5, Proposition 2: convergence of coherent erasure

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.5, Proposition 2: the averaged channel converges in trace norm and has the
anchor as its unique supported fixed density. K>=2 makes the displayed average defined. -/
theorem proposition2_erasure (phi : K → EuclideanSpace ℂ I) (a : K)
    (hK : 2 ≤ Fintype.card K) (hphi : ∀ k, IsState (phi k))
    (hgen : Generates (pureSamples phi)) :
    (∀ rho, IsDensityMatrix rho → InSampleSupport (pureSamples phi) rho →
      Tendsto (fun T : ℕ => traceNorm
        ((coherentErasureChannel (nonanchorProbability a) (erasureGate phi a))^[T] rho -
          pureDensity (phi a))) atTop (nhds 0)) ∧
    (∀ rho, IsDensityMatrix rho → InSampleSupport (pureSamples phi) rho →
      coherentErasureChannel (nonanchorProbability a) (erasureGate phi a) rho = rho →
        rho = pureDensity (phi a)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
