-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_classicalTypical
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.classicalTypical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:21:47.072711+00:00
-- url     : https://prove2.me/theorems/daad6c59-7b57-4b06-b213-9092bb49e3c6
-- title:
--   Lemma I.8: Pr(TV,P,alpha)≥1−a/alpha² and |TV,P,alpha|≤2^(nH(P)+K a alpha sqrt(n)), K=2log2(e)/e.
-- statement:
--   Let $X$ be a finite nonempty alphabet of size $a$, $P$ a normalized law, $n>0$ and $\alpha>0$. A word is variance typical if each count differs from $nP(x)$ by at most $\alpha\sqrt{nP(x)(1-P(x))}$. Put $K_V=2\log_2(e)/e$.
--
--   $$
--   P^{\otimes n}(T_{V,P,\alpha}^n)\ge1-a/\alpha^2,\qquad |T_{V,P,\alpha}^n|\le2^{nH(P)+K_Va\alpha\sqrt n}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 11, Lemma I.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma I.8, PDF pp.11-12. Printed d in the cardinality bound is corrected to
alphabet size a: the proof is the eigenvalue-list counting argument, and there is no
quantum dimension in this classical statement. See MODERATION_NOTES.md. -/
theorem classicalTypical {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : PMF I) (n : ℕ) (hn : 0 < n) (alpha : ℝ) (halpha : 0 < alpha) :
    (∑ w ∈ varianceSet P n alpha, ∏ k, (P (w k)).toReal) ≥
      1 - Fintype.card I / alpha^2 ∧
    ((varianceSet P n alpha).card : ℝ) ≤
      exp2 (n * pmfEntropy P + varianceConstant * Fintype.card I * alpha * Real.sqrt n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
