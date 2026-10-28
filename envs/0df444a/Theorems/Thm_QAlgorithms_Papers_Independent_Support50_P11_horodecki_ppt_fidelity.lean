-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_horodecki_ppt_fidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P11.horodecki_ppt_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:06:49.307883+00:00
-- url     : https://prove2.me/theorems/b2f02da9-1a52-4e4c-b24c-2531f3bed72d
-- title:
--   Proposition 6: PPTp fidelity over a Horodecki channel
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel between positive finite-dimensional systems whose Choi matrix has positive partial transpose, and let $K\ge1$. For actual forward-assisted PPT-preserving codes, the optimal normalized entanglement fidelity is
--   $$F^{\mathrm{PPTp}}(\mathcal N,K)=\frac1K.$$
--   The claim is about the optimum over codes. It includes the scalar case $K=1$, and forward classical assistance is permitted in this class.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 8, Proposition 6: PPTp fidelity over a Horodecki channel

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section Statements

variable {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]

/-- PDF p.8, Proposition 6: the optimal PPTp channel fidelity over a Horodecki
channel is 1/K, not the optimalCodeFidelity of every individual code. -/
theorem horodecki_ppt_fidelity
    (N : Superop I O) (hN : Horodecki N) (K : ℕ) (hK : 0 < K) :
    optimalCodeFidelity .PPTp N K = 1 / (K : ℝ) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
