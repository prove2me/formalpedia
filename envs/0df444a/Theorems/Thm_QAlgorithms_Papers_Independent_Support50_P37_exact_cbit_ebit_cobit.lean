-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_exact_cbit_ebit_cobit
-- name    : QAlgorithms.Papers.Independent.Support50.P37.exact_cbit_ebit_cobit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:53:18.44759+00:00
-- url     : https://prove2.me/theorems/9a6ca64e-7cad-4bc5-9be8-4380ee358e02
-- title:
--   One cbit and one ebit exactly simulate one cobit
-- statement:
--   A forward cbit is the dephasing channel obtained from $|x\rangle_A\mapsto|x\rangle_B|x\rangle_E$ with inaccessible environment $E$. A forward cobit is the coherent isometry $|x\rangle_A\mapsto|x\rangle_A|x\rangle_B$, for $x\in\{0,1\}$. An ebit is the normalized shared pair $(|00\rangle+|11\rangle)/\sqrt2$.
--
--   Using free local quantum operations, one use of the cbit channel and one supplied ebit exactly simulate one cobit:
--   $$
--   1\ \mathrm{cbit}+1\ \mathrm{ebit}\ \succeq\ 1\ \mathrm{cobit}.
--   $$
--   The conversion holds in either direction. It is a finite single-bit transformation, with equality on every input operator and hence every reference extension. No other nonlocal call or borrowed catalyst is supplied. This conversion permits replacing consumed cobits by explicitly charged classical communication and entanglement.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 8, Eq. (30)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Eq.(30): exact finite simulation of a cobit using one cbit and one
supplied EPR pair, in either direction. Every other nonlocal call count is zero.
Exact requires equality on all input operators, hence on all reference extensions. -/
theorem exact_cbit_ebit_cobit :
    Exact (idle 1 1) (budget 0 1 0 0 0 0 1 0) (cobitChannel 2) ∧
    Exact (idle 1 1) (budget 0 1 0 0 0 0 0 1) (reverse (cobitChannel 2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
