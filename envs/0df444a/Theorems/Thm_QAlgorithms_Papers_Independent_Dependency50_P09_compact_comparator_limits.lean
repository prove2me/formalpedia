-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_compact_comparator_limits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.compact_comparator_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:12:44.591728+00:00
-- url     : https://prove2.me/theorems/3657d9ee-7fba-46bb-8e6d-4f900e47946d
-- title:
--   Proposition 36
-- statement:
--   Let $N:A\to B$ be CPTP and $\mathcal C$ any compact set of CP maps on the same positive-dimensional finite ports. Compactness is in the finite-dimensional matrix-unit coefficient topology, equivalently any norm topology on linear maps. The set may be empty. Every displayed expression is a limit of an infimum, with a two-sided positive-order approach to one.
--
--   $$
--   \lim_{\alpha\to1}\inf_{M\in\mathcal C}D_\alpha(N\Vert M)=\inf_{M\in\mathcal C}D(N\Vert M),\quad\lim_{\alpha\to1}\inf_{M\in\mathcal C}\widetilde D_\alpha(N\Vert M)=\inf_{M\in\mathcal C}D(N\Vert M),\quad\lim_{\alpha\to1}\inf_{M\in\mathcal C}\widehat D_\alpha(N\Vert M)=\inf_{M\in\mathcal C}\widehat D(N\Vert M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The accent at order one in (466) denotes Umegaki; empty C gives +infinity on both sides. Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 28, Proposition 36

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 36, arXiv:2010.01058v3, PDF pp.28.
The accent at order one in (466) denotes Umegaki; empty C gives +infinity on both sides. Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). Printed: The order-one entropy in (466) has an undefined tilde. Changed: Use Umegaki relative entropy. Why: The order-one limit (152) identifies Umegaki; (472) repeats the same limit argument. -/
theorem compact_comparator_limits {I : Type} [Fintype I] [Nonempty I]
    {J : Type} [Fintype J] [Nonempty J]
    (N : Superop I J) (hN : IsChannel N) (K : Set (MapCoefficients I J))
    (hK : IsCompact K) (hCP : ∀ M ∈ K, CP (coeffMap M)) :
    Tendsto (fun alpha : ℝ => ⨅ M : K, channelD (petzD alpha) N (coeffMap M.1))
        orderOne (𝓝 (⨅ M : K, channelD relativeD N (coeffMap M.1))) ∧
      Tendsto (fun alpha : ℝ => ⨅ M : K, channelD (sandwichedD alpha) N (coeffMap M.1))
        orderOne (𝓝 (⨅ M : K, channelD relativeD N (coeffMap M.1))) ∧
      Tendsto (fun alpha : ℝ => ⨅ M : K, channelD (geometricD alpha) N (coeffMap M.1))
        orderOne (𝓝 (⨅ M : K, channelD bsD N (coeffMap M.1))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
