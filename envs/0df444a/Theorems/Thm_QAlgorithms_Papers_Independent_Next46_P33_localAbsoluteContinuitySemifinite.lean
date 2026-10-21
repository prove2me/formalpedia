-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P33_localAbsoluteContinuitySemifinite
-- name    : QAlgorithms.Papers.Independent.Next46.P33.localAbsoluteContinuitySemifinite
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:30:45.996316+00:00
-- url     : https://prove2.me/theorems/40039194-0f06-470a-b6b7-bccebaa51fed
-- title:
--   Local absolute continuity makes a normal weight semifinite
-- statement:
--   Let $M$ be a von Neumann algebra with normal weights $\phi_0$ and $\phi_1$, where $\phi_1$ is faithful and semifinite. Suppose that every projection having finite $\phi_1$-weight also has finite $\phi_0$-weight. Then
--
--   $$
--   \phi_0\text{ is semifinite}.
--   $$
--
--   Semifiniteness means that the complex linear span of the positive elements with finite weight is ultraweakly dense in $M$. This permits the paper's later support reductions without initially assuming semifiniteness of $\phi_0$.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, PDF p. 6, Remark 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Remark 3.6, PDF p.6. A normal locally absolutely continuous weight
relative to an fns weight is itself semifinite. This is a conclusion, not an
assumption on phi0. -/
theorem localAbsoluteContinuitySemifinite
    (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hNormal1 : IsNormalWeight phi1) (hFaithful1 : IsFaithfulWeight phi1)
    (hSemifinite1 : IsSemifiniteWeight phi1) (hNormal0 : IsNormalWeight phi0)
    (hLocal : WeightLocallyAbsolutelyContinuous phi0 phi1) :
    IsSemifiniteWeight phi0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P33

end
