-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_corollaryIV5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.corollaryIV5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:27:08.770142+00:00
-- url     : https://prove2.me/theorems/6b348f62-89d5-46b4-9584-0bf250282148
-- title:
--   Infinite-order capacities as suprema
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For $t=*$ or $t=\flat$,
--   $$\chi^t_\infty(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\infty,1}(W,P)
--   =\sup_{P\in\mathcal P_f(X)}\chi^t_{\infty,2}(W,P)
--   =\sup_{\alpha>1}\chi^t_\alpha(W).$$
--
--
--   This identifies both infinite-order information optimizations with the finite-order capacity supremum.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 22, Corollary IV.5 For (t) = ∗ and (t) = ♭,

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

/-- Corollary IV.5, PDF p.22 (91): b and star infinite-order capacities,
including the supremum over both fixed-law information types. -/
theorem corollaryIV5 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (t : Flavor) (ht : t = .star ∨ t = .b) :
    cqRenyiCapacity t ⊤ W = (⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t ⊤ 0 W p.1) ∧
    cqRenyiCapacity t ⊤ W = (⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t ⊤ 1 W p.1) ∧
    cqRenyiCapacity t ⊤ W = (⨆ a : {a : ℝ // 1 < a}, cqRenyiCapacity t a.1 W) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
