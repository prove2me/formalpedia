-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionIV2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionIV2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:26:09.403273+00:00
-- url     : https://prove2.me/theorems/14d316b6-9e74-453b-aaf2-1a3281e6fb3b
-- title:
--   Equality of regularized radius and the two optimized information types
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For the Petz family at $0<\alpha\le2$, the star family at $\alpha\ge1/2$ of finite order, and the b family at $\alpha>1$,
--   $$R^t_\alpha(W)=\sup_{\varepsilon>0}\inf_{\sigma\in\mathcal S(H)}\sup_{x\in X}D^t_\alpha(W(x)\|\sigma+\varepsilon I)
--   =\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,2}(W,P)
--   =\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)=\chi^t_\alpha(W).$$
--   For $t=\flat$ and $0<\alpha<1$, the two displayed finite-law suprema are also equal to each other.
--
--   All four main identifications are retained without requiring a finite input alphabet.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 20, Proposition IV.2 We have

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

/-- Proposition IV.2, PDF pp.20-22 (86)-(89), with all four formulas and the
additional low-order b equality. Alphabet X is arbitrary. -/
theorem propositionIV2 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) :
    (∀ (t : Flavor) (a : ℝ), CapacityRange t a →
      cqRenyiRadius t a W =
        ⨆ e : {e : ℝ // 0 < e}, ⨅ sigma : {A : Mat I // IsDensityMatrix A},
          ⨆ x, renyiValue t a (W x) (sigma.1 + (e.1 : ℂ) • 1)) ∧
    (∀ (t : Flavor) (a : ℝ), CapacityRange t a →
      cqRenyiRadius t a W = ⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t a 1 W p.1) ∧
    (∀ (t : Flavor) (a : ℝ), CapacityRange t a →
      (⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t a 1 W p.1) =
        ⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t a 0 W p.1) ∧
    (∀ (t : Flavor) (a : ℝ), CapacityRange t a → cqRenyiRadius t a W = cqRenyiCapacity t a W) ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      (⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation .b a 1 W p.1) =
        ⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation .b a 0 W p.1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
