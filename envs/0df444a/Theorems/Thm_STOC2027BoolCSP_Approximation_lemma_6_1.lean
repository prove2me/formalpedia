-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_lemma_6_1
-- name    : STOC2027BoolCSP.Approximation.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:09.471502+00:00
-- url     : https://prove2.me/theorems/a5c7a342-fd7b-48f5-bf8d-6ddf92309146
-- title:
--   Lemma 6.1 — clause probability
-- statement:
--   Fix $k\ge5$, a signed $k$-conjunction instance and a feasible vector solution $(e,(d_i),(z_C))$ of the common-reference relaxation (5) in some finite-dimensional real space. Run the rounding (28)–(29) with $m=k+1$, $\delta=\pi/m$ and a single reference score $S_0$. Then for every clause $C$, with $q_C=\|z_C\|^2$,
--   $$\Pr(C\text{ is satisfied})\;\ge\;\alpha_k\,q_C,\qquad \alpha_k=\frac{k+1}{2^k}.$$
--
--   Summed with nonnegative weights this gives $\mathbb E\,\mathrm{val}(x)\ge\alpha_kV$ for every feasible objective value $V$ (equation (31)). Linearity of expectation needs no independence between clauses.
--
--   Differences from the source:
--
--   - encoding: a feasible solution of (5) and a standard Gaussian g in the joint vector space → a vector family in ι → ℝ for an arbitrary finite type ι with the dot product, g ∼ product of standard normals on ι → ℝ; reason: every feasible Gram matrix is realized by vectors in dimension D, and every finite-dimensional real inner product space is isometric to some ℝ^ι
--   - encoding: sgn(S) with ties of probability zero → sgn(0) = +1; reason: ties form a null event in the ideal rounding, so the probability is unchanged
--   - generalization: Section 2 normalization gives nonnegative conjunction weights summing to one → arbitrary rational conjunction weights; reason: vector feasibility, rounding and the individual clause probability do not depend on weights; every normalized source instance is included
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 12 (PDF 15), Lemma 6.1 (rounding (28)–(29))

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation

/-- Lemma 6.1 (clause probability), printed p. 12: for every feasible vector solution of (5) and
every conjunction `C`, the shared-reference rounding (28)–(29) satisfies
`Pr(C satisfied) ≥ α_k q_C`. -/
theorem lemma_6_1 (k : ℕ) (hk : 5 ≤ k) (C : ConjInstance k) (ι : Type) [Fintype ι]
    (v : Idx C.n C.M → ι → ℝ) (hv : C.VecFeasible v) (c : Fin C.M) :
    alpha k * (v (zIdx c) ⬝ᵥ v (zIdx c)) ≤ C.clauseProb v c := by sorry

end STOC2027BoolCSP.Approximation
