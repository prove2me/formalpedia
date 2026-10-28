-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_code_inclusions_and_performance
-- name    : QAlgorithms.Papers.Independent.Support50.P11.code_inclusions_and_performance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:03:20.561741+00:00
-- url     : https://prove2.me/theorems/53145a6c-142b-48fd-a014-ac25e627f14f
-- title:
--   §III (17)–(19): inclusions and performance monotonicity
-- statement:
--   Let $\mathcal N:A'\to B$ be a finite-dimensional CPTP channel and $K\ge1$. Codes are actual CPTP bipartite operations from the sender's $K$-dimensional system and $B$ to $A'$ and the receiver's $K$-dimensional system, non-signalling from Bob to Alice. Write UA, EA, FCA, FHA, NS and PPTp for unassisted, entanglement-assisted, forward-classical-assisted, forward-Horodecki-assisted, non-signalling and PPT-preserving codes. Their inclusions are
--   $$\mathrm{UA}\subseteq\mathrm{EA}\subseteq\mathrm{NS},\qquad
--   \mathrm{UA}\subseteq\mathrm{FCA}\subseteq\mathrm{FHA}\subseteq\mathrm{PPTp}.$$
--   Consequently their optimal channel fidelities satisfy
--   $$F^{\mathrm{UA}}\le F^{\mathrm{EA}}\le F^{\mathrm{NS}},\qquad F^{\mathrm{UA}}\le F^{\mathrm{FCA}}\le F^{\mathrm{FHA}}\le F^{\mathrm{PPTp}},$$
--   at $(\mathcal N,K)$, and their operational memoryless quantum capacities satisfy the identical two chains. These comparisons transport operational performance through the code inclusions.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 5, §III (17)–(19): inclusions and performance monotonicity

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

/-- PDF p.5, (17)--(19): class inclusions, finite-size fidelity monotonicity,
and the corresponding operational quantumCodeCapacity inequalities. There is no EA/PPTp inclusion. -/
theorem code_inclusions_and_performance
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K) :
    (∀ Z : Superop (Fin K × O) (I × Fin K),
      (IsForwardCode K .UA Z → IsForwardCode K .EA Z) ∧
      (IsForwardCode K .EA Z → IsForwardCode K .NS Z) ∧
      (IsForwardCode K .UA Z → IsForwardCode K .FCA Z) ∧
      (IsForwardCode K .FCA Z → IsForwardCode K .FHA Z) ∧
      (IsForwardCode K .FHA Z → IsForwardCode K .PPTp Z)) ∧
    optimalCodeFidelity .UA N K ≤ optimalCodeFidelity .EA N K ∧ optimalCodeFidelity .EA N K ≤ optimalCodeFidelity .NS N K ∧
    optimalCodeFidelity .UA N K ≤ optimalCodeFidelity .FCA N K ∧ optimalCodeFidelity .FCA N K ≤ optimalCodeFidelity .FHA N K ∧
    optimalCodeFidelity .FHA N K ≤ optimalCodeFidelity .PPTp N K ∧
    quantumCodeCapacity .UA N ≤ quantumCodeCapacity .EA N ∧ quantumCodeCapacity .EA N ≤ quantumCodeCapacity .NS N ∧
    quantumCodeCapacity .UA N ≤ quantumCodeCapacity .FCA N ∧ quantumCodeCapacity .FCA N ≤ quantumCodeCapacity .FHA N ∧
    quantumCodeCapacity .FHA N ≤ quantumCodeCapacity .PPTp N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
