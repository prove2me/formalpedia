-- Prove2me | Theorems.Thm_PrescribedPointCount_exists_isElliptic_trace_eq_of_dvd
-- name    : PrescribedPointCount.exists_isElliptic_trace_eq_of_dvd
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T19:26:31.724208+00:00
-- url     : https://prove2.me/theorems/54ea88bc-1f6e-4c2b-8176-abeb5c6bd2f2
-- title:
--   Deuring existence over $\mathbb{F}_p$: supersingular traces
-- statement:
--   Let $p$ be a prime number and let $t\in\mathbb{Z}$ be an integer with
--
--   $$t^2\le 4p\qquad\text{and}\qquad p\mid t.$$
--
--   Then there exists an elliptic curve $E$ over $\mathbb{F}_p$ whose Frobenius trace equals $t$:
--
--   $$p+1-\#E(\mathbb{F}_p)=t.$$
--
--   The condition $p\mid t$ says that the sought curve is **supersingular**. For a prime field the two hypotheses force $t=0$, or $p\in\{2,3\}$ with $t=\pm p$; the statement asserts that each of these traces is realized. This is the supersingular case of Deuring's existence theorem (1941), and the cases $t=0$ and $t=\pm p^{(n+1)/2}$ ($n=1$, $p=2,3$) of Waterhouse's classification (1969, Thm 4.1). Together with the ordinary case ($p\nmid t$) it yields every trace in the Hasse interval, hence the mission's goal.
--
--   **Formalization Note.** The trace is written in $\mathbb{Z}$ as $(p:\mathbb{Z})+1-\#E$ to avoid truncated natural-number subtraction. `E.IsElliptic` is nonzero discriminant over the field `ZMod p`; `Nat.card E.toAffine.Point` is the number of affine rational points plus the point at infinity. The hypotheses are satisfiable for every prime $p$ (take $t=0$).
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197-272, https://doi.org/10.1007/BF02940746 (existence of curves of every trace over F_p; supersingular case). W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. ÉNS (4) 2 (1969), 521-560, Theorem 4.1, cases t=0 and n odd, p=2 or 3, t=±p^{(n+1)/2}, https://www.numdam.org/item/ASENS_1969_4_2_4_521_0/. See also L. C. Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., CRC Press, 2008, Section 4.6 (Supersingular Curves).

import Mathlib

namespace PrescribedPointCount

theorem exists_isElliptic_trace_eq_of_dvd (p : ℕ) [Fact p.Prime] (t : ℤ)
    (ht : t ^ 2 ≤ 4 * (p : ℤ)) (hpt : (p : ℤ) ∣ t) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by sorry

end PrescribedPointCount
