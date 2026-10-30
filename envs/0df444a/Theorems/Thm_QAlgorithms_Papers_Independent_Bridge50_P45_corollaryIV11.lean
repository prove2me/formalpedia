-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_corollaryIV11
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.corollaryIV11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:30:12.660972+00:00
-- url     : https://prove2.me/theorems/7c454ce4-cf13-4d52-bdb0-cd0eaf8af9a7
-- title:
--   Normalized first-type pinched information limits
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For each blocklength $n$, choose a universal symmetric state $\sigma_{u,n}$ as in Lemma II.8: it is permutation invariant and central in the invariant algebra, dominates every symmetric density operator by a factor $v_{n,d}$, and has at most $v_{n,d}$ distinct eigenvalues, where $d=\dim H$ and $v_{n,d}\le(n+1)^{(d+2)(d-1)/2}$. Write $\mathcal E_n$ for pinching by this state.
--
--   For every $P\in\mathcal P_f(X)$ and $\alpha>1$,
--   $$\lim_{n\to\infty}\frac1n\chi^\flat_{\alpha,1}(\mathcal E_nW^{\otimes n},P^{\otimes n})
--   =\lim_{n\to\infty}\frac1n\chi_{\alpha,1}(\mathcal E_nW^{\otimes n},P^{\otimes n})
--   =\chi^*_{\alpha,1}(W,P).$$
--
--
--   This is a fixed-law first-type information limit, rather than a second-type or capacity limit.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 25, Corollary IV.11 For every P ∈ Pf (X ) and every α > 1,

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

/-- Corollary IV.11, PDF p.25 (103): two first-type fixed-law limits.
No second-type or optimized-capacity limit is substituted. -/
theorem corollaryIV11 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (p : X → ℝ) (hp : FiniteInputLaw p)
    (a : ℝ) (ha : 1 < a) (U : (n : ℕ) → Universal I n) :
    Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      fixedLawInformation .b a 0 (pinchedChannel W n (U n)) (independentInputLaw p n)) atTop
      (𝓝 (fixedLawInformation .star a 0 W p)) ∧
    Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      fixedLawInformation .petz a 0 (pinchedChannel W n (U n)) (independentInputLaw p n)) atTop
      (𝓝 (fixedLawInformation .star a 0 W p)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
