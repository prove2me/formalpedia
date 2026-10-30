-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_conversion_order
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.conversion_order
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:14:41.070767+00:00
-- url     : https://prove2.me/theorems/bc4c47d7-e349-411a-822e-1279ea827cde
-- title:
--   Corollary III.4, equations (3)–(5): conversion order
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Bell pairs shared by the first two parties are the currency. Integer copy counts are nonnegative, blocklengths are positive, and both approximation error and the uniform global-robustness leakage tend to zero absolutely. Let $\rho$ and $\sigma$ be states on possibly different systems, including different party counts; omitted parties are trivial. A conversion consists of CPTP maps $\Lambda_n$ and integers $0\le d_n\le n$ with $d_n/n\to0$, vanishing uniform robustness leakage, and $\|\Lambda_n(\rho^{\otimes n})-\sigma^{\otimes(n-d_n)}\|_1\to0$. Then
--
--   $$\rho\prec\sigma\quad\Longleftrightarrow\quad E_R^\infty(\rho)\ge E_R^\infty(\sigma).$$
--
--   This characterizes the full conversion order, including both free and entangled states. It assumes neither an optimizing sequence nor a positive rate.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 7, Corollary III.4, equations (3)–(5): conversion order

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.7, Corollary III.4, Eqs.(3)–(5): the full conversion order,
including free states and unrelated finite input/output party counts. -/
theorem conversion_order {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (rho : PartyOperator A) (sigma : PartyOperator B)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    AsymptoticConverts A rho B sigma ↔ regularizedMultipartiteEntanglement B sigma ≤
      regularizedMultipartiteEntanglement A rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
