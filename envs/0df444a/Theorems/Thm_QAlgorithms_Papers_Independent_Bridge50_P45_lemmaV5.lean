-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaV5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaV5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:32:04.695571+00:00
-- url     : https://prove2.me/theorems/b66f884e-f0e0-4ca0-9527-56c5949ef14f
-- title:
--   Optimality lower bound for the strong converse exponent
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For positive blocklength $n$ and positive message count $M$, a code uses a deterministic encoder into $X^n$ and one $M$-outcome POVM; its success is the uniform-message average $P_s=M^{-1}\sum_k\operatorname{Tr}W^{\otimes n}(\varphi(k))D(k)$. A real $r$ is $R$-achievable if one code sequence satisfies both $\liminf_n n^{-1}\log M_n\ge R$ and $\liminf_n n^{-1}\log P_s\ge-r$. The operational exponent $\operatorname{sc}(R,W)$ is the infimum of all such $r$, with $\log0=-\infty$. Put $H^t_{R,c}(W)=\sup_{\alpha>1}(\alpha-1)\{R-\chi^t_\alpha(W)\}/\alpha$.
--
--   For every $R\ge0$,
--   $$\operatorname{sc}(R,W)\ge H^*_{R,c}(W).$$
--
--
--   This is the optimality direction, distinct from the full exponent equality.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 27, Lemma V.5 For any classical-quantum channel W ∈ C(H|X ) and R ≥ 0, we have

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Nonempty X] [Nonempty I]

/-- Lemma V.5, PDF pp.27-28 (109): optimality direction, with nonnegative rate. -/
theorem lemmaV5 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (R : ℝ) (hR : 0 ≤ R) :
    converseCapacityTransform .star W R ≤ sc W R := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
