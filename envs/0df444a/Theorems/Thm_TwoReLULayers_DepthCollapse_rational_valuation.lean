-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_rational_valuation
-- name    : TwoReLULayers.DepthCollapse.rational_valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:27.447284+00:00
-- url     : https://prove2.me/theorems/0e7a236a-0578-44f6-8798-110466ea07bd
-- title:
--   Rational subdivision corrections preserve vertices and coefficients
-- statement:
--   Let $n\ge2$ and let $A\subseteq E_n$ be a $d$-dimensional affine space spanned by rational points. Let the $P_i\subseteq A$ be nonempty rational polytopes and let $c_i\in\mathbb Q$. If $\sum_i c_i1_{P_i}=0$ geometrically almost everywhere on $A$, then
--   $$\sum_i c_i h_{P_i}\in\operatorname{span}_{\mathbb Q}\{h_Q:Q\subseteq A\text{ nonempty rational polytope},\ \dim Q\le d-1\}.$$
--   This states the rational specialization of the common-subdivision correction argument required by Section 8's rational-weight conclusion. It supplements, rather than restricts or replaces, the full real Corollary 16.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - generalization: rational lower-dimensional corrections for the explicit rational construction → rational corrections for arbitrary rational polytopes and rational coefficients in a rational affine space; reason: the same finite common rational subdivision applies to any such inputs and includes all constructed indicator relations
--   - encoding: rational vertices and rational affine data → membership in the bottom subfield of ℝ in IsPolytopeOver and RationalAffine; reason: the prime subfield of ℝ is exactly ℚ; these predicates require actual finite rational generating sets
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 24, Section 8, final paragraph, with Corollary 16 proof, p. 21 (unnumbered rational bridge)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem rational_valuation {n k d : ℕ} (hn : 2 ≤ n)
    (A : AffineSubspace ℝ (E n)) (hA : RationalAffine A)
    (hd : Module.finrank ℝ A.direction = d)
    (P : Fin k → Set (E n)) (c : Fin k → ℚ)
    (hP : ∀ i, IsPolytopeOver (⊥ : Subfield ℝ) (P i) ∧ P i ⊆ A)
    (hcancel : GeomAE A (fun y => ∑ i, (c i : ℝ) * indicator (P i) y = 0)) :
    (fun x => ∑ i, (c i : ℝ) * support (P i) x) ∈
      rationalSpanOn (A : Set (E n)) ((d : ℤ) - 1) := by sorry

end TwoReLULayers.DepthCollapse
