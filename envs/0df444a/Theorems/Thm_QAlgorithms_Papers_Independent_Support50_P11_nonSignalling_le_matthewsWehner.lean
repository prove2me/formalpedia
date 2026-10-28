-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_nonSignalling_le_matthewsWehner
-- name    : QAlgorithms.Papers.Independent.Support50.P11.nonSignalling_le_matthewsWehner
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:08:35.159303+00:00
-- url     : https://prove2.me/theorems/1ebea71e-8078-4df6-9da6-ac7c87314455
-- title:
--   §V (45)–(48): comparison with the Matthews–Wehner bound
-- statement:
--   Let $\mathcal N:A'\to B$ be finite CPTP and $K\ge1$. Write $N$ for its unnormalized Choi matrix, and define $B(\mathcal N,M)$ as the supremum of $\operatorname{Re}\operatorname{Tr}(N^T\Lambda)$ over density matrices $\rho$ and operators satisfying
--   $$0\preceq\Lambda\preceq\rho\otimes I_B,\qquad\operatorname{Tr}_{A'}\Lambda\preceq I_B/M.$$
--   Then
--   $$F^{\mathrm{EA}}(\mathcal N,K)\le F^{\mathrm{NS}}(\mathcal N,K)\le B(\mathcal N,K^2).$$
--   The relaxation is an operator inequality on the marginal, retaining the same full-transpose objective. This compares the NS bound with the Matthews–Wehner bound in the form used here.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 8, §V (45)–(48): comparison with the Matthews–Wehner bound

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

/-- PDF p.8, (45)--(48): the NS optimum lies below the relaxed SDP whose
marginal equality is replaced by a Loewner inequality. The (47) class typo is EA. -/
theorem nonSignalling_le_matthewsWehner
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K) :
    optimalCodeFidelity .EA N K ≤ optimalCodeFidelity .NS N K ∧ optimalCodeFidelity .NS N K ≤ relaxedBound N (K * K) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
