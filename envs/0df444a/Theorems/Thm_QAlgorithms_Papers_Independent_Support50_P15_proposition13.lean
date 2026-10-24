-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_proposition13
-- name    : QAlgorithms.Papers.Independent.Support50.P15.proposition13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:49:33.604608+00:00
-- url     : https://prove2.me/theorems/5365b640-b2c8-4e81-8a9b-2d545f4c2c9b
-- title:
--   Capacity from the spread of column entropies
-- statement:
--   Let $T:X\to Y$ be a normalized discrete memoryless channel with nonempty input alphabet and finite output cardinality $d=|Y|\ge2$. Capacity is measured in nats as the supremum of single-letter mutual information over finite-support input laws. Put $S_{\min}=\inf_x S(T(\cdot|x))$, $S_{\max}=\sup_x S(T(\cdot|x))$, $a=S_{\max}-S_{\min}$ and $L=\log^2(d-1)+4$. Then
--
--   $$C(T)\ge\frac{a^2}{2L}-\frac{a^3}{3L^2}.$$
--
--   If the fixed-dimensional asymmetry statement of Conjecture 12 holds, also $C(T)\ge M(-a/2,d)$. Finite input alphabets have attained column extrema; supremal and infimal entropies give the same statement for arbitrary nonempty discrete input, without an unmentioned finiteness assumption. This supplies a capacity lower bound from column entropy spread alone.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 15, proposition13

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Proposition 13, PDF p.15. Arbitrary nonempty discrete input; finite output; capacity in nats.
Supremal/infimal column entropies allow nonattained extrema. -/
theorem proposition13 {X : Type*} [Nonempty X] {d : ℕ} (hd : 2 ≤ d) (c : FiniteOutputChannel X d) :
    let lo := sInf (Set.range (fun x => shannonEntropyNats (c.prob x)))
    let hi := sSup (Set.range (fun x => shannonEntropyNats (c.prob x)))
    redundancyBound d (hi - lo) ≤ finiteOutputCapacityNats c ∧
    (asymmetryConjecture d → tightBound d (-(hi - lo) / 2) ≤ (finiteOutputCapacityNats c : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
