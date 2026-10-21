-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_lemma3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.lemma3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:56:21.741011+00:00
-- url     : https://prove2.me/theorems/6e7fb142-1e16-4957-8254-eebcb1f2f6f2
-- title:
--   Lemma 3: linear independence on a small measurable set
-- statement:
--   Let $f_1,\ldots,f_n:[a,b]\to\mathbb C$ be Lebesgue measurable and linearly independent modulo almost-everywhere equality. Thus a combination $\sum_i c_i f_i$ equal to zero almost everywhere on $[a,b]$ has every coefficient $c_i=0$. For every $\epsilon>0$ there is a Lebesgue measurable set $A\subseteq[a,b]$ such that
--
--   $$\mu(A)<\epsilon,\qquad f_1|_A,\ldots,f_n|_A\text{ are linearly independent modulo a.e. equality}.$$
--
--   Here $\mu$ is Lebesgue measure. There is no integrability or square-integrability hypothesis. For an empty family the independence condition is vacuous, including on the empty set.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 17, Lemma 3: linear independence on a small measurable set

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.17–18, Lemma 3. Independence is modulo equality
a.e., not pointwise nonvanishing a.e. Completion measurability means Lebesgue
measurability; no Borel-only restriction or L¹/L² assumption is added. -/
theorem lemma3 {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℂ)
    (hmeas : ∀ i, AEMeasurable (f i) (volume.restrict (Set.Icc a b)))
    (hind : aeIndependent f (Set.Icc a b)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : Set ℝ, A ⊆ Set.Icc a b ∧ NullMeasurableSet A volume ∧
      volume A < ENNReal.ofReal epsilon ∧ aeIndependent f A := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
