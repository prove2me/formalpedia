-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_theorem_1_3
-- name    : STOC2027BoolCSP.Approximation.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:34.917064+00:00
-- url     : https://prove2.me/theorems/168d3d51-13e0-494c-90dd-dc1fc3ece090
-- title:
--   Theorem 1.3 — exact relaxation gap: $\inf_{\mathrm{OPT}>0}\mathrm{OPT}/\mathrm{SDP}=\alpha_k$, attained by the all-sign-pattern instance
-- statement:
--   Fix $k\ge5$, $\alpha_k=(k+1)/2^k$, and let $\mathrm{SDP}(I)$ be the value of the common-reference relaxation (5): the supremum of $\sum_C w_Cq_C$ over positive semidefinite Gram matrices of vectors $e,d_1,\dots,d_n,(z_C)_C$ with $\langle e,e\rangle=\langle d_i,d_i\rangle=1$, $q_C=\langle z_C,z_C\rangle=\langle e,z_C\rangle$ and $\langle\sigma_{C,i}d_i,z_C\rangle=q_C$ for $i\in C$. Then:
--
--   1. every instance $I$ of signed $k$-conjunctions with nonnegative rational weights and $\mathrm{OPT}(I)>0$ has $\mathrm{SDP}(I)>0$ and
--   $$\frac{\mathrm{OPT}(I)}{\mathrm{SDP}(I)}\ \ge\ \alpha_k ;$$
--   2. for every rational $w>0$, the instance on $k$ variables containing all $2^k$ signed $k$-literal conjunctions, each of weight $w$, has $\mathrm{OPT}>0$, $\mathrm{SDP}>0$ and $\mathrm{OPT}/\mathrm{SDP}=\alpha_k$.
--
--   Together,
--   $$\inf_{I:\ \mathrm{OPT}(I)>0}\frac{\mathrm{OPT}(I)}{\mathrm{SDP}(I)}=\alpha_k,$$
--   and the infimum is attained.
--
--   The gap instance shows that the rounding analysis of the mission's goal is exact relative to this relaxation.
--
--   Differences from the source:
--   - reading: infimum over instances I → over weighted signed-k-conjunction instances (exactly k distinct variables per clause, nonnegative rational weights, not normalized); reason: Section 3's relaxation is defined on the expanded conjunction instances; it is homogeneous in the weights
--   - encoding: inf OPT/SDP = α_k, attained by the all-sign instance → (1) every instance with OPT > 0 has SDP > 0 and OPT/SDP ≥ α_k, and (2) the all-sign instance has OPT/SDP = α_k; reason: an attained infimum is a least element
--   - reading: all 2^k signed k-literal conjunctions with equal weight → every common positive rational weight w; reason: the theorem fixes no value; Section 9's weight one is the case w = 1
--   - encoding: the 2^k sign patterns σ → indices 0, …, 2^k − 1, position j carrying binary digit j; reason: a bijection onto {−1,1}^k
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 2 (PDF 5), Theorem 1.3; proof printed p. 21 (PDF 24), Section 9; relaxation printed p. 6 (PDF 9), equation (5)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_ConjOpt

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- Theorem 1.3 (exact relaxation gap), printed p. 2, proof §9. For every `k ≥ 5`:
(i) every signed-`k`-conjunction instance with nonnegative rational weights and `OPT > 0`
satisfies `OPT ≥ α_k · SDP` for the common-reference relaxation (5); (ii) for every positive
rational weight `w`, the instance on `k` variables with all `2^k` signed `k`-literal conjunctions,
each of weight `w`, has `OPT > 0` and `OPT = α_k · SDP`. Together: `inf_{OPT>0} OPT/SDP = α_k`,
attained. -/
theorem theorem_1_3 (k : ℕ) (hk : 5 ≤ k) :
    (∀ C : ConjInstance k, (∀ c, 0 ≤ C.w c) → 0 < conjOpt C →
        0 < C.sdpValue ∧ alpha k ≤ conjOpt C / C.sdpValue) ∧
    (∀ w : ℚ, 0 < w →
        0 < conjOpt (allSignInstance k w) ∧ 0 < (allSignInstance k w).sdpValue ∧
        conjOpt (allSignInstance k w) / (allSignInstance k w).sdpValue = alpha k) := by sorry

end STOC2027BoolCSP.Approximation.Supplement
