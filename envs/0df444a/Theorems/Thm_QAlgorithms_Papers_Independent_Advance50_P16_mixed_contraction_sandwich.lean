-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_mixed_contraction_sandwich
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.mixed_contraction_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:34:32.270985+00:00
-- url     : https://prove2.me/theorems/a884ea39-ecac-44f9-9585-465a66180e1f
-- title:
--   Lemma 9: mixed-norm contraction sandwich
-- statement:
--   Let $1\le q\le p\le\infty$ and let $C,D,X$ be arbitrary complex matrices on a nonzero finite tensor-product register. If $\|X\|_\infty\le1$, then
--
--   $$\|C^\dagger XD\|_{(q,p)}\le\bigl(\|C^\dagger C\|_{(q,p)}\,\|D^\dagger D\|_{(q,p)}\bigr)^{1/2}.$$
--
--   Here the mixed norms are the vector-valued norms of (3.2)–(3.3), and infinity is a genuine exponent endpoint. Both right-hand factors lie inside the square root. This inequality is the positivity-reduction tool used for finite CB amplifications.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 17, Lemma 9: mixed-norm contraction sandwich

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Lemma 9 / (3.25), PDF p.17: both factors are under the square root;
C,D,X are arbitrary complex matrices, and only X is required to be a contraction. -/
theorem mixed_contraction_sandwich {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (q p : ℝ≥0∞) (hq : 1 ≤ q) (hqp : q ≤ p)
    (C Dm X : Mat (D × I)) (hX : specNorm X ≤ 1) :
    mixedNorm q p (Cᴴ * X * Dm) ≤
      Real.sqrt (mixedNorm q p (Cᴴ * C) * mixedNorm q p (Dmᴴ * Dm)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
