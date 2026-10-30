-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_theoremV12
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.theoremV12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:36:37.971583+00:00
-- url     : https://prove2.me/theorems/1fa4d04e-7d98-4e19-bdfe-52ddf42e25e5
-- title:
--   Exact fixed-law variational expression for the dummy cost
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For a law $P$, let $D(V\|W\mid P)=\sum_xP(x)D(V(x)\|W(x))$, where $V$ ranges over cq channels on the same alphabet and output space. Define $F(P,R,W)=\inf_V\{D(V\|W\mid P)+\max(0,R-\chi(V,P))\}$, $F_1(P,R,W)=\inf_{V:\chi(V,P)>R}D(V\|W\mid P)$, and $F_2(P,R,W)=\inf_{V:\chi(V,P)\le R}\{D(V\|W\mid P)+R-\chi(V,P)\}$. Empty feasible sets have infimum $+\infty$.
--
--   For $R\ge0$ and $P\in\mathcal P_f(X)$,
--   $$F(P,R,W)=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\{R-\chi^\flat_{\alpha,2}(W,P)\}.$$
--
--
--   The transform uses second-type fixed-law b information and includes rate zero.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 31, Theorem V.12 Given W ∈ C(H|X ) and R ≥ 0, for any P ∈ Pf (X ), we have

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

/-- Theorem V.12, PDF pp.31-33 (122): the SECOND-type b information occurs
inside the fixed-law transform, including rate zero. -/
theorem theoremV12 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (R : ℝ) (hR : 0 ≤ R)
    (p : X → ℝ) (hp : FiniteInputLaw p) :
    dummyF p R W = ⨆ a : {a : ℝ // 1 < a},
      (((a.1-1)/a.1 : ℝ) : EReal) * ((R : EReal) - fixedLawInformation .b a.1 1 W p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
