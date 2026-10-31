-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_klm_threefoldPorts
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.klm_threefoldPorts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:33:03.661656+00:00
-- url     : https://prove2.me/theorems/8411c877-1891-4142-9db6-640d033e55d2
-- title:
--   Threefold port overhead for equal quoted KLM success
-- statement:
--   Let $N,m\ge1$ be integer port counts. Compare the correction-free qubit success curve $p_{\rm PBT}(N)=N/(N+3)$ from (56) with the KLM curve $p_{\rm KLM}(m)=1-1/(m+1)$ quoted by the paper from [17]. Then
--
--   $$p_{\rm PBT}(N)=p_{\rm KLM}(m)\quad\Longleftrightarrow\quad N=3m.$$
--
--   This is the present paper's comparison of the two supplied curves; it does not independently assert or certify a KLM circuit construction.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 8, §VI B, comparison after Eq. (56)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.8, §VI B: comparison with the KLM curve quoted from [17].
This is the equality of the two supplied curves, not a theorem about KLM circuits. -/
theorem klm_threefoldPorts (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) :
    probabilisticOptimumSuccess N = klmCurve m ↔ N = 3 * m := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
