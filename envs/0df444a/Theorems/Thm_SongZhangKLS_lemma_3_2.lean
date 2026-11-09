-- Prove2me | Theorems.Thm_SongZhangKLS_lemma_3_2
-- name    : SongZhangKLS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:32.076196+00:00
-- url     : https://prove2.me/theorems/6114e474-9b81-4fd4-8956-9800287fa9a2
-- title:
--   Lemma 3.2 — reduction to regular measures: $C_P(\mu)\le(1+\delta)C_P(\nu)+\delta$ for a regular isotropic log-concave $\nu$
-- statement:
--   Let $\mu$ be an isotropic log-concave probability measure on $\mathbb R^n$. For every $0<\delta<1$, there is a regular isotropic log-concave probability measure $\nu$ on $\mathbb R^n$ such that
--   $$C_P(\mu)\le(1+\delta)\,C_P(\nu)+\delta.$$
--
--   Consequently a bound $C_P(\nu)\le C$ for all regular isotropic log-concave $\nu$ transfers to every isotropic log-concave $\mu$, which is how the main theorem removes the regularity assumption of Theorem 5.1.
--
--   **Formalization Note** Regular is Definition 3.1. The inequality is read in $[0,\infty]$, since $C_P(\nu)$ is not known to be finite a priori.
--
--   Differences from the source:
--   - encoding: log-concave: $\mu(sA+(1-s)B)\ge\mu(A)^s\mu(B)^{1-s}$ for compact $A,B$ and $0\le s\le1$ → the published `FunctionalInequalities.KLS.LogConcave` (the same inequality for $0<s<1$); reason: the endpoints $s\in\{0,1\}$ are trivial for every measure under the paper's conventions, while the literal $s=0$, $A=\emptyset$ case with the convention $0^0=1$ would exclude every measure; same class
--   - encoding: isotropic: $\int x\,d\mu=0$ and $\int x\otimes x\,d\mu=I_n$ → the published `FunctionalInequalities.KLS.Isotropic` (finite second moment, mean $0$, centered covariance operator the identity); reason: finite second moments are implicit in the source's definition; same measures
--   - encoding: $C_P(\mu)\in[0,+\infty]$, the least $C$ in (1) with the $L^2$ requirement, $+\infty$ if no finite $C$ works → `poincareConst`: an infimum in $[0,\infty]$ over finite $C\ge0$ (empty infimum $=\infty$), with $\nabla f$ the Mathlib `gradient` and the variance `evariance`; reason: Lean convention; the variance is nonnegative so only $C\ge0$ matter, and for measures absolutely continuous with respect to Lebesgue measure the gradient of a locally Lipschitz function exists almost everywhere (Rademacher); same values
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_poincareConst
import Definitions.Def_SongZhangKLS_IsRegular

open MeasureTheory
open scoped ENNReal

namespace SongZhangKLS

/-- **Lemma 3.2 (Reduction from general to regular isotropic measures)**, p.12, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `µ` be an isotropic log-concave probability measure on `ℝⁿ`. For every `0 < δ < 1`, there
is a regular isotropic log-concave probability measure `ν` such that
`C_P(µ) ≤ (1 + δ) C_P(ν) + δ`.

**Formalization Note.** `ν` lives on the same `ℝⁿ`. Poincaré constants are `poincareConst` in
`ℝ≥0∞` (eq. (1), with the `L²` requirement), and the inequality is read in `ℝ≥0∞`. Regular is
Definition 3.1 (`IsRegular`); log-concave and isotropic are the published
`FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`. -/
theorem lemma_3_2 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave μ)
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      IsRegular (ν : Measure (EuclideanSpace ℝ (Fin n))) ∧
      FunctionalInequalities.KLS.Isotropic ν ∧ FunctionalInequalities.KLS.LogConcave ν ∧
      poincareConst (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        (1 + ENNReal.ofReal δ) * poincareConst (ν : Measure (EuclideanSpace ℝ (Fin n))) +
          ENNReal.ofReal δ := by sorry

end SongZhangKLS
