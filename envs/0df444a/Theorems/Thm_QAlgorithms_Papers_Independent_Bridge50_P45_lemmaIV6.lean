-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIV6
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIV6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:28:04.561907+00:00
-- url     : https://prove2.me/theorems/4e5ee48a-247b-4a80-bb1b-2e9ffccd08ab
-- title:
--   Order monotonicity and limits of information and capacity
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For every family $t$, law $P\in\mathcal P_f(X)$, and $i=1,2$, $\chi^t_{\alpha,i}(W,P)$ and $\chi^t_\alpha(W)$ are monotone increasing on $(0,\infty]$, and
--   $$\chi(W,P)=\lim_{\alpha\downarrow1}\chi^t_{\alpha,i}(W,P)=\inf_{\alpha>1}\chi^t_{\alpha,i}(W,P),$$
--   $$\chi^t_{\infty,i}(W,P)=\lim_{\alpha\to\infty}\chi^t_{\alpha,i}(W,P)=\sup_{\alpha>1}\chi^t_{\alpha,i}(W,P),$$
--   $$\chi^t_\infty(W)=\lim_{\alpha\to\infty}\chi^t_\alpha(W)=\sup_{\alpha>1}\chi^t_\alpha(W),\qquad
--   \chi(W)=\lim_{\alpha\downarrow1}\chi^t_\alpha(W)=\inf_{\alpha>1}\chi^t_\alpha(W).$$
--
--
--   The capacity-at-one limit from the continuation on PDF p.23 is included, along with the fixed-law limits.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 22, Lemma IV.6 For all three values of (t), any P ∈ Pf (X ), and i = 1, 2, α 7→ χα,i (W, P ) is monotone

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

/-- Lemma IV.6, PDF pp.22-23 (92)-(95). Both fixed-law information types,
capacity limits at one and infinity, and every infimum/supremum identity are retained. -/
theorem lemmaIV6 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (t : Flavor)
    (p : X → ℝ) (hp : FiniteInputLaw p) (i : Fin 2) :
    MonotoneOn (fun a : EReal => fixedLawInformation t a i W p) (Ioi 0) ∧
    Tendsto (fun a : ℝ => fixedLawInformation t a i W p) (𝓝[>] 1) (𝓝 (ordinaryLawInformation W p)) ∧
    ordinaryLawInformation W p = (⨅ a : {a : ℝ // 1 < a}, fixedLawInformation t a.1 i W p) ∧
    Tendsto (fun a : ℝ => fixedLawInformation t a i W p) atTop (𝓝 (fixedLawInformation t ⊤ i W p)) ∧
    fixedLawInformation t ⊤ i W p = (⨆ a : {a : ℝ // 1 < a}, fixedLawInformation t a.1 i W p) ∧
    MonotoneOn (fun a : EReal => cqRenyiCapacity t a W) (Ioi 0) ∧
    Tendsto (fun a : ℝ => cqRenyiCapacity t a W) atTop (𝓝 (cqRenyiCapacity t ⊤ W)) ∧
    cqRenyiCapacity t ⊤ W = (⨆ a : {a : ℝ // 1 < a}, cqRenyiCapacity t a.1 W) ∧
    Tendsto (fun a : ℝ => cqRenyiCapacity t a W) (𝓝[>] 1) (𝓝 (cqRenyiCapacity .petz 1 W)) ∧
    cqRenyiCapacity .petz 1 W = (⨅ a : {a : ℝ // 1 < a}, cqRenyiCapacity t a.1 W) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
