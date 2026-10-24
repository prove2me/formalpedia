-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_nonSignalling_capacity_eq_entanglementAssisted
-- name    : QAlgorithms.Papers.Independent.Support50.P11.nonSignalling_capacity_eq_entanglementAssisted
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:02:29.206224+00:00
-- url     : https://prove2.me/theorems/21c1f8bc-67a1-4f9e-b339-de82d2bfa5c9
-- title:
--   Abstract main result; §V (49): non-signalling and entanglement-assisted quantum capacities coincide
-- statement:
--   Let $\mathcal N:A'\to B$ be any CPTP channel between positive finite-dimensional systems with fixed computational bases. For assistance class $\Omega$, let $F^\Omega(\mathcal N,K)$ be the supremum of normalized entanglement fidelities of actual forward-assisted bipartite codes of size $K$. Define the operational memoryless capacity by
--   $$Q^\Omega(\mathcal N)=\sup\{r\ge0:\lim_{n\to\infty}F^\Omega(\mathcal N^{\otimes n},\lfloor2^{nr}\rfloor)=1\}.$$
--   Here NS imposes non-signalling in both directions on the code, and EA permits arbitrary shared states and local operations. Then
--   $$Q^{\mathrm{NS}}(\mathcal N)=Q^{\mathrm{EA}}(\mathcal N).$$
--   The equality concerns parallel memoryless blocks and operational vanishing entanglement error, with rates in qubits per use.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 8, Abstract main result; §V (49): non-signalling and entanglement-assisted quantum capacities coincide

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

/-- PDF p.8, (49), abstract p.1: the two operational memoryless quantum capacities coincide. -/
theorem nonSignalling_capacity_eq_entanglementAssisted
    (N : Superop I O) (hN : IsChannel N) : quantumCodeCapacity .NS N = quantumCodeCapacity .EA N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
