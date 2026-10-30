-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIV10
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIV10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:29:33.841899+00:00
-- url     : https://prove2.me/theorems/eda8bbf2-0a6d-449a-82da-8ac18081d47d
-- title:
--   Two quantitative lower bounds for pinched b information
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For each blocklength $n$, choose a universal symmetric state $\sigma_{u,n}$ as in Lemma II.8: it is permutation invariant and central in the invariant algebra, dominates every symmetric density operator by a factor $v_{n,d}$, and has at most $v_{n,d}$ distinct eigenvalues, where $d=\dim H$ and $v_{n,d}\le(n+1)^{(d+2)(d-1)/2}$. Write $\mathcal E_n$ for pinching by this state.
--
--   For every $P\in\mathcal P_f(X)$, $\alpha>1$, $i=1,2$, and $n\in\mathbb N$,
--   $$\chi^\flat_{\alpha,i}(\mathcal E_nW^{\otimes n},P^{\otimes n})\ge
--   \chi_{\alpha,i}(\mathcal E_nW^{\otimes n},P^{\otimes n})-\log v_{n,d},$$
--   $$\chi^\flat_{\alpha,i}(\mathcal E_nW^{\otimes n},P^{\otimes n})\ge
--   \chi^*_{\alpha,i}(W^{\otimes n},P^{\otimes n})-3\log v_{n,d}.$$
--
--
--   The first comparison is with the pinched Petz channel and the second with the original star channel; the constants are exact.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 25, Lemma IV.10 For every P ∈ Pf (X ), every α > 1, and i = 1, 2,

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

/-- Lemma IV.10, PDF p.25 (100). The Petz comparison uses the PINCHED channel;
the star comparison uses the original product channel. Constants are exactly 1 and 3. -/
theorem lemmaIV10 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (p : X → ℝ) (hp : FiniteInputLaw p)
    (a : ℝ) (ha : 1 < a) (i : Fin 2) (n : ℕ) (U : Universal I n) :
    fixedLawInformation .petz a i (pinchedChannel W n U) (independentInputLaw p n) - (Real.log U.v : EReal) ≤
      fixedLawInformation .b a i (pinchedChannel W n U) (independentInputLaw p n) ∧
    fixedLawInformation .star a i (memorylessOutputs W n) (independentInputLaw p n) - ((3 * Real.log U.v : ℝ) : EReal) ≤
      fixedLawInformation .b a i (pinchedChannel W n U) (independentInputLaw p n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
