-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_quantum_classical_fidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P11.quantum_classical_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:07:44.404645+00:00
-- url     : https://prove2.me/theorems/1a8ae852-a8a9-41a8-a5fb-a74d0b66406e
-- title:
--   §V (46): quantum/classical fidelity correspondence for EA and NS
-- statement:
--   Let $\mathcal N:A'\to B$ be a finite-dimensional CPTP channel and $K\ge1$. Let $F^\Omega(\mathcal N,K)$ be the optimal normalized channel fidelity for a $K$-dimensional quantum system, and let $P_s^\Omega(\mathcal N,M)$ be the optimal average success probability for $M$ equiprobable computational-basis messages, both optimized over actual codes in class $\Omega$. Then
--   $$F^{\mathrm{EA}}(\mathcal N,K)=P_s^{\mathrm{EA}}(\mathcal N,K^2),\qquad
--   F^{\mathrm{NS}}(\mathcal N,K)=P_s^{\mathrm{NS}}(\mathcal N,K^2).$$
--   This is exact fidelity preservation for the two operational classes used in the paper. No unspecified conversion loss is introduced.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 8, §V (46): quantum/classical fidelity correspondence for EA and NS

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

/-- PDF p.8, (46), supported by Appendix B, pp.14--15: exact classical/quantum
performance correspondence for the two named operational classes EA and NS. -/
theorem quantum_classical_fidelity
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K) :
    optimalCodeFidelity .EA N K = optimalClassicalCodeFidelity .EA N (K * K) ∧
    optimalCodeFidelity .NS N K = optimalClassicalCodeFidelity .NS N (K * K) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
