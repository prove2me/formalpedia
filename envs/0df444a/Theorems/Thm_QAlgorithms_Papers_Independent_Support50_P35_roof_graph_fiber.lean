-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_roof_graph_fiber
-- name    : QAlgorithms.Papers.Independent.Support50.P35.roof_graph_fiber
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:37:23.940203+00:00
-- url     : https://prove2.me/theorems/852a1cdb-b4b8-44a8-ba4a-278b0c4c3cf1
-- title:
--   Both roofs are graph-hull fiber extrema
-- statement:
--   Let \(V\subseteq\mathbb R^n\) be a nonempty compact irreducible nonsingular real affine algebraic variety, let \(f:V\to\mathbb R\) be continuous, and let \(r\in\operatorname{conv}V\). Define the lower and upper roofs by the infimum and supremum, respectively, of \(\sum_{j=1}^m p_jf(x_j)\) over every positive finite length \(m\), points \(x_j\in V\), and real weights \(p_j\geq0\) with \(\sum_jp_j=1\) and \(\sum_jp_jx_j=r\). Writing \(\Gamma_f=\{(x,f(x)):x\in V\}\), one has
--
--   $$
--   \operatorname{conv}f(r)=\inf\{t:(r,t)\in\operatorname{conv}\Gamma_f\},\qquad
--   \operatorname{conc}f(r)=\sup\{t:(r,t)\in\operatorname{conv}\Gamma_f\}.
--   $$
--
--   The hull is the finite convex hull. Compactness and continuity make the fiber nonempty and bounded, so these are actual finite real extrema values. This identifies the roofs with the lower and upper fiber boundaries.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 5, Lemma 2.2: roofs are graph-hull fiber extrema

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF pp.5--6, Lemma 2.2: both roofs are extrema of the actual finite
convex-hull fiber. All standing variety and continuity assumptions are retained. -/
theorem roof_graph_fiber {n : ℕ} (V : Set (Fin n → ℝ))
    (hV : IsNonsingularVariety V) (hcompact : IsCompact V) (hne : V.Nonempty)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f V)
    (r : Fin n → ℝ) (hr : r ∈ convexHull ℝ V) :
    lowerRoof V f r = sInf {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} ∧
    upperRoof V f r = sSup {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
