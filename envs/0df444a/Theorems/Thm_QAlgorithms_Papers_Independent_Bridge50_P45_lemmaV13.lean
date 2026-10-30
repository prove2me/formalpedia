-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaV13
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaV13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:37:26.725059+00:00
-- url     : https://prove2.me/theorems/7e7b537b-0c39-4d0b-af33-40c96f2d8bf9
-- title:
--   Minimax interchange for both b information types
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For positive blocklength $n$ and positive message count $M$, a code uses a deterministic encoder into $X^n$ and one $M$-outcome POVM; its success is the uniform-message average $P_s=M^{-1}\sum_k\operatorname{Tr}W^{\otimes n}(\varphi(k))D(k)$. A real $r$ is $R$-achievable if one code sequence satisfies both $\liminf_n n^{-1}\log M_n\ge R$ and $\liminf_n n^{-1}\log P_s\ge-r$. The operational exponent $\operatorname{sc}(R,W)$ is the infimum of all such $r$, with $\log0=-\infty$. Put $H^t_{R,c}(W)=\sup_{\alpha>1}(\alpha-1)\{R-\chi^t_\alpha(W)\}/\alpha$.
--
--   For $R\ge0$ and either $i=1$ or $i=2$,
--   $$H^\flat_{R,c}(W)=\sup_{\alpha>1}\inf_{P\in\mathcal P_f(X)}\frac{\alpha-1}{\alpha}\{R-\chi^\flat_{\alpha,i}(W,P)\}
--   =\inf_{P\in\mathcal P_f(X)}\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\{R-\chi^\flat_{\alpha,i}(W,P)\}.$$
--   The law optimization remains an infimum and need not be attained.
--
--   This permits the fixed-law dummy-channel bound to be optimized over arbitrary alphabets.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 33, Lemma V.13 For every R ≥ 0,

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

/-- Lemma V.13, PDF pp.33-34 (134): both information types, and an infimum
rather than a minimum over all finite-support laws on arbitrary X. -/
theorem lemmaV13 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (R : ℝ) (hR : 0 ≤ R) (i : Fin 2) :
    converseCapacityTransform .b W R = (⨆ a : {a : ℝ // 1 < a}, ⨅ p : {p : X → ℝ // FiniteInputLaw p},
      (((a.1-1)/a.1 : ℝ) : EReal) * ((R : EReal) - fixedLawInformation .b a.1 i W p.1)) ∧
    converseCapacityTransform .b W R = (⨅ p : {p : X → ℝ // FiniteInputLaw p}, ⨆ a : {a : ℝ // 1 < a},
      (((a.1-1)/a.1 : ℝ) : EReal) * ((R : EReal) - fixedLawInformation .b a.1 i W p.1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
