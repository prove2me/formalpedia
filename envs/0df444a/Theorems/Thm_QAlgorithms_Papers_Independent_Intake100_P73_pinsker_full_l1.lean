-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_pinsker_full_l1
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.pinsker_full_l1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:59:32.409833+00:00
-- url     : https://prove2.me/theorems/115f6c5f-c75e-4b73-b209-623860ff8a1a
-- title:
--   Pinsker inequality in the source full-L1/nats convention
-- statement:
--   For any probability mass functions p and q on an arbitrary discrete alphabet, full L1 distance d(p,q)=sum_y |p(y)-q(y)| and extended KL divergence D(p||q) in natural logarithms satisfy d(p,q)^2/2 <= D(p||q). Support mismatch gives infinite divergence; zero-mass summands follow the standard continuous convention. The printed coefficient 1 is corrected to 1/2.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 10, §VI.A: Pinsker inequality (normalization audit)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi PDF p.10, background Pinsker inequality. Printed: D>=full-L1^2.
Changed: D>=full-L1^2/2, because the source uses full L1 and natural logarithms.
No finite-alphabet or absolute-continuity restriction is added. -/
theorem pinsker_full_l1 {Omega : Type*} (p q : PMF Omega) :
    fullL1 p q ^ 2 / 2 ≤ discreteKLDivergence p q := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
