-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_classical_triples_region
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.classical_triples_region
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:04:48.399802+00:00
-- url     : https://prove2.me/theorems/358e0ba4-c835-496f-80e2-c1d2391bde46
-- title:
--   Sec. III B, unnumbered: exact classical analogue joinability region
-- statement:
--   Let $d\ge2$ be an integer and $a,b,c\in[0,1]$. For $\alpha\in[0,1]$, define $p_\alpha(i,j)=\alpha/d$ if $i=j$, and $(1-\alpha)/(d(d-1))$ otherwise. The AB, AC, BC distributions $p_a,p_b,p_c$ have a nonnegative normalized joint distribution exactly when
--   $$(a,b,c)\in\operatorname{conv}\{(1,1,1),(1,0,0),(0,1,0),(0,0,1)\}$$
--   for $d=2$; for $d\ge3$ include the additional vertex $(0,0,0)$ in this hull. The assertion characterizes attainable pair marginals; it does not require every joint law to be exchange symmetric.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 7, Sec. III B, unnumbered: exact classical analogue joinability region

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.III B, PDF pp.7–8: exact attainable classical parameter region.
This is a statement about marginals; it does not assert symmetry of every joining law. -/
theorem classical_triples_region (d : ℕ) (hd : 2 ≤ d) (a b c : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    ClassicalTripleJoinable d a b c ↔ ![a,b,c] ∈ convexHull ℝ (classicalVertices d) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
