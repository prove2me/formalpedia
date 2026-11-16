-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_3_6
-- name    : QMomentMatch.FirstBound.Supplement.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:13.916113+00:00
-- url     : https://prove2.me/theorems/99693397-bc72-41b6-aae5-4a05c64a02d9
-- title:
--   Lemma 3.6 — inverse binomial moments: $\mathbb E[(1+Y)^{-1}]=\frac{1-(1-a)^m}{ma}$ and $\mathbb E[(1+Y)^{-\beta}(1+Z)^{-\gamma}]\le(ma)^{-\beta}(mb)^{-\gamma}$ for any coupling
-- statement:
--   Let $m\ge1$ be an integer, let $a,b\in(0,1]$, and let $Y,Z$ be random variables (on a common probability space, not necessarily independent) with marginal laws $Y\sim\mathrm{Bin}(m-1,a)$ and $Z\sim\mathrm{Bin}(m-1,b)$. Then
--   $$\mathbb E\big[(1+Y)^{-1}\big]=\frac{1-(1-a)^m}{ma}\le\frac1{ma},$$
--   and for all real $\beta,\gamma\ge0$ with $\beta+\gamma\le1$,
--   $$\mathbb E\big[(1+Y)^{-\beta}(1+Z)^{-\gamma}\big]\le(ma)^{-\beta}(mb)^{-\gamma}.$$
--
--   In the proof of Lemma 4.1 this averages the inverse block-count factors of Lemma 4.9 over the random multiplicities, where the counts of different values are dependent.
--
--   **Formalization Note** The pair $(Y,Z)$ is given by its joint law $\mu$ on $\{0,\dots,m-1\}^2$, an arbitrary probability vector whose two marginals are the binomial laws; every coupling of $Y$ and $Z$ has such a joint law, and the expectations depend only on it.
--
--   Differences from the source:
--   - encoding: random variables Y, Z with marginals Bin(m−1, a), Bin(m−1, b), not necessarily independent → an arbitrary probability vector μ on Fin m × Fin m whose marginals are binomPmf (m−1) a and binomPmf (m−1) b; reason: both expectations depend only on the joint law, which is supported on {0,…,m−1}²
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.6, pp. 17–18

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff

namespace QMomentMatch.FirstBound.Supplement

open QMomentMatch.FirstBound

/-- Lemma 3.6 (Inverse binomial moments), pp. 17–18. The pair `(Y, Z)` is given by its joint
law `μ` on `{0, …, m−1}²` (any coupling), whose marginals are `Bin(m − 1, a)` and
`Bin(m − 1, b)`. -/
theorem lemma_3_6 (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (μ : Fin m × Fin m → ℝ) (hμ : IsProbVec μ)
    (hY : ∀ y : Fin m, ∑ z : Fin m, μ (y, z) = binomPmf (m - 1) a y)
    (hZ : ∀ z : Fin m, ∑ y : Fin m, μ (y, z) = binomPmf (m - 1) b z) :
    ∑ p : Fin m × Fin m, μ p * (1 + ((p.1 : ℕ) : ℝ))⁻¹ = (1 - (1 - a) ^ m) / ((m : ℝ) * a) ∧
    (1 - (1 - a) ^ m) / ((m : ℝ) * a) ≤ 1 / ((m : ℝ) * a) ∧
    ∀ β γ : ℝ, 0 ≤ β → 0 ≤ γ → β + γ ≤ 1 →
      ∑ p : Fin m × Fin m, μ p * ((1 + ((p.1 : ℕ) : ℝ)) ^ (-β) * (1 + ((p.2 : ℕ) : ℝ)) ^ (-γ)) ≤
        ((m : ℝ) * a) ^ (-β) * ((m : ℝ) * b) ^ (-γ) := by sorry

end QMomentMatch.FirstBound.Supplement
