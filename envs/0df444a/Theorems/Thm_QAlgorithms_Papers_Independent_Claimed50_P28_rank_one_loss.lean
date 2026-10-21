-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_rank_one_loss
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.rank_one_loss
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:20:52.067497+00:00
-- url     : https://prove2.me/theorems/a4917002-079b-4549-9e5f-2bc8f40cc1b5
-- title:
--   Rank-one loss formulas with target-dependent admissibility
-- statement:
--   Let $d\ge2$ and let normalized positive rank-one seeds have total trace $d$. Suppose their Haar frame $F$ is complete on the selected target span. Write $m=d^2-1$ and let $A$ be the coefficient in (29). Then $B=A$, $C=(1-2A)/m$, and $0\le A\le1/(d+1)<1/2$. Operations and general channels require $A>0$; unital tomography permits $A=0$. The minimum over admissible linear reconstruction duals is attained and equals $\operatorname{Tr}(F^\ddagger Q_K)$, namely
--
--   $$\eta_{\mathcal Q}=1+m\left(\frac2A+\frac{m^2}{1-2A}\right),\qquad\eta_{\mathcal C}=1+m\left(\frac1A+\frac{m^2}{1-2A}\right),\qquad\eta_{\mathcal U}=1+\frac{m^3}{1-2A}.$$
--
--   Here $F^\ddagger$ is the inverse on the frame support and zero on its kernel, while $Q_K$ projects onto the required complex target span. Completeness excludes a kernel direction in that span. Thus real division at $A=0$ is never used for the operation or channel formulas.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (33): optimized dual loss for rank-one seeds and the admissible A range.
Operations and channels require A>0; the unital target allows A=0 and a singular full frame. -/
theorem rank_one_loss {d : ℕ} (hd : 2 ≤ d) (K : TomographyDomain)
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (hP : Seeds P) (hrank : ∀ j, RankOneSeed (P j))
    (hcomplete : FrameComplete (twirledFrame haar P) K) :
    let A := coefficientA P
    0 ≤ A ∧ A ≤ 1 / ((d : ℝ) + 1) ∧ 1 / ((d : ℝ) + 1) < 1/2 ∧
    (K ≠ .unital → 0 < A) ∧ coefficientB P = A ∧
    coefficientC P = (1 - 2*A) / ((d : ℝ)^2 - 1) ∧
    (frameSupportInverse (twirledFrame haar P) * targetProjector d K).trace.re = rankOneLoss d K A ∧
    (∀ D, TomographyAdmissible (Measure.count.prod (haar.prod haar)) (covariant P) D K →
      rankOneLoss d K A ≤ eta K (Measure.count.prod (haar.prod haar)) (covariant P) D) ∧
    ∃ D, TomographyAdmissible (Measure.count.prod (haar.prod haar)) (covariant P) D K ∧
      eta K (Measure.count.prod (haar.prod haar)) (covariant P) D = rankOneLoss d K A := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
