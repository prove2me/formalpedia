-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_poissonized_probe_tail
-- name    : QuadraticProbe717.Insertion.poissonized_probe_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:55.6075+00:00
-- url     : https://prove2.me/theorems/6e2c6d41-885f-4514-9671-3302dfcf6d47
-- title:
--   Proposition 5.1 — Poissonized insertion tail
-- statement:
--   Let $n$ be prime, $0<\varepsilon<1$, and $1<k\le n/2$. Let $T$ be the next insertion cost in the algorithm-generated Poissonized table of mean $(1-\varepsilon)n$. Then
--   $$\Pr[T>k]\le e^{-\varepsilon k/8}+\frac{8R(k)}{\varepsilon^2k^2},\qquad\Pr[T>k]\le\frac{43R(k)}{\varepsilon^2k^2}.$$
--   The first inequality is the proof's explicit estimate on pp. 10–11. The second fixes a uniform representative of the stated big-O bound: $R(k)\ge1$ for $k>1$, and $\sup_{x>0}x^2e^{-x/8}=256/e^2<35$. No table-dependent constant is allowed.
--
--   Differences from the source:
--   - encoding: Poisson((1−ε)n) insertions including N≥n → the discrete mixture of algorithm-generated occupied-set laws with Poisson rate ((1−ε)n).toNNReal; reason: 0<ε<1 makes the rate exact; full tables remain full and subsequent costs are 2n
--   - encoding: O(R(k)/(ε²k²)) and the explicit exponential-plus-covariance estimate in its proof → both the proof estimate and its consequence with absolute constant 43; reason: 43=35+8; this preserves the source uniform bound and exposes a valid explicit constant
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Proposition 5.1, equation (5); explicit estimate pp. 10–11, p. 9 (PDF p. 9)

import Definitions.Def_QuadraticProbe717_Insertion_laws
import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem poissonized_probe_tail (n : ℕ) [NeZero n] (hn : n.Prime)
    (π : Equiv.Perm (ZMod n)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (hk : 1 < k) (hkn : 2 * k ≤ n) :
    poissonTail n π (poissonRate n ε) k ≤
      Real.exp (-ε * k / 8) + 8 * multiplicity n k / (ε^2 * (k : ℝ)^2) ∧
    poissonTail n π (poissonRate n ε) k ≤
      43 * multiplicity n k / (ε^2 * (k : ℝ)^2) := by sorry

end QuadraticProbe717.Insertion
