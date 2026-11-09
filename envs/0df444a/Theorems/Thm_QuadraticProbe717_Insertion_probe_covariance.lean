-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_probe_covariance
-- name    : QuadraticProbe717.Insertion.probe_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:05.977663+00:00
-- url     : https://prove2.me/theorems/ccf0f00f-0547-46a6-97a0-0fd44cdfc67e
-- title:
--   Proposition 4.1 — covariance along quadratic probes
-- statement:
--   Let $n$ be prime, $0<\varepsilon<1$, and $1\le k\le n/2$. In the Poissonized table put $C(r)=\operatorname{Cov}(F_0,F_r)$, and let $R(k)$ be the maximum square-difference multiplicity over nonzero residues. Then
--   $$\sum_{0\le a<b<k} C(b^2-a^2)\le R(k).$$
--   Each pair is counted once, and every subtraction is modulo $n$. The bound has coefficient one, including the empty sum when $k=1$.
--
--   Differences from the source:
--   - encoding: Poisson((1−ε)n) insertions including N≥n → the discrete mixture of algorithm-generated occupied-set laws with Poisson rate ((1−ε)n).toNNReal; reason: 0<ε<1 makes the rate exact; full tables remain full and subsequent costs are 2n
--   - encoding: 0≤a<b<k and k≤n/2 → a,b in Fin k with a<b, and 2k≤n; reason: the double sum uses zero for the other ordered pairs and counts exactly the source pairs
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Proposition 4.1, p. 8 (PDF p. 8)

import Definitions.Def_QuadraticProbe717_Insertion_laws
import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem probe_covariance (n : ℕ) [NeZero n] (hn : n.Prime)
    (π : Equiv.Perm (ZMod n)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (∑ a : Fin k, ∑ b : Fin k, if a < b then
      vacancyCovariance n π (poissonRate n ε) ((b.val : ZMod n)^2 - (a.val : ZMod n)^2)
      else 0) ≤ (multiplicity n k : ℝ) := by sorry

end QuadraticProbe717.Insertion
