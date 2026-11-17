-- Prove2me | Theorems.Thm_PrescribedPointCount_exists_isElliptic_trace_eq_of_not_dvd
-- name    : PrescribedPointCount.exists_isElliptic_trace_eq_of_not_dvd
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T19:26:20.050244+00:00
-- url     : https://prove2.me/theorems/ea509098-dc43-47f7-84df-369f6234940a
-- title:
--   Deuring existence over $\mathbb{F}_p$: ordinary traces
-- statement:
--   Let $p$ be a prime number and let $t\in\mathbb{Z}$ be an integer with
--
--   $$t^2\le 4p\qquad\text{and}\qquad p\nmid t.$$
--
--   Then there exists an elliptic curve $E$ over $\mathbb{F}_p$ whose Frobenius trace equals $t$:
--
--   $$p+1-\#E(\mathbb{F}_p)=t.$$
--
--   The condition $t^2\le 4p$ is the integer form of the Hasse bound $|t|\le 2\sqrt{p}$, and $p\nmid t$ says that the sought curve is **ordinary**. This is the ordinary case of Deuring's existence theorem (1941): Deuring constructs such a curve by reducing a characteristic-zero elliptic curve with complex multiplication by an order of discriminant $t^2-4p$ modulo a prime above $p$ (his reduction and lifting theorems); it is also the case $\gcd(t,p)=1$ of Waterhouse's classification (1969, Thm 4.1). Together with the supersingular case ($p\mid t$) it yields every trace in the Hasse interval, hence the mission's goal.
--
--   **Formalization Note.** The trace is written in $\mathbb{Z}$ as $(p:\mathbb{Z})+1-\#E$ to avoid truncated natural-number subtraction. `E.IsElliptic` is nonzero discriminant over the field `ZMod p`; `Nat.card E.toAffine.Point` is the number of affine rational points plus the point at infinity.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197-272, https://doi.org/10.1007/BF02940746 (existence of curves of every trace over F_p; ordinary case via CM reduction). W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. ÉNS (4) 2 (1969), 521-560, Theorem 4.1, case gcd(t,p)=1, https://www.numdam.org/item/ASENS_1969_4_2_4_521_0/. See also L. C. Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., CRC Press, 2008, Chapter 4.

import Mathlib

namespace PrescribedPointCount

theorem exists_isElliptic_trace_eq_of_not_dvd (p : ℕ) [Fact p.Prime] (t : ℤ)
    (ht : t ^ 2 ≤ 4 * (p : ℤ)) (hpt : ¬ (p : ℤ) ∣ t) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by sorry

end PrescribedPointCount
