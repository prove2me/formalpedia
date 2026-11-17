-- Prove2me | Theorems.Thm_PrescribedPointCount_exists_isElliptic_natCard_point_eq
-- name    : PrescribedPointCount.exists_isElliptic_natCard_point_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T19:26:45.86586+00:00
-- url     : https://prove2.me/theorems/844678d7-9986-4515-8a1b-8bd27605923d
-- title:
--   Elliptic curves with a prescribed point count over $\mathbb{F}_p$
-- statement:
--   Let $p$ be a prime number and let $N$ be a natural number lying strictly inside the **Hasse interval**,
--
--   $$|N-(p+1)|<2\sqrt{p}.$$
--
--   Then there exists an elliptic curve $E$ over $\mathbb{F}_p$ whose group of $\mathbb{F}_p$-rational points has exactly $N$ elements:
--
--   $$\#E(\mathbb{F}_p)=N.$$
--
--   Equivalently, every integer $t$ with $|t|<2\sqrt{p}$ is the Frobenius trace $p+1-\#E(\mathbb{F}_p)$ of some elliptic curve over $\mathbb{F}_p$ (take $t=p+1-N$). This is Deuring's existence theorem (1941) over prime fields, and it is the mathematical core of the FrontierMath open problem *Elliptic curves with a prescribed point count*, which asks for an **efficient** construction of such a curve even when the CM discriminant $D=(p+1-N)^2-4p$ has a large squarefree part. Since $p$ is prime, $2\sqrt{p}$ is irrational, so for integer $N$ the strict inequality is equivalent to the closed Hasse bound $|N-(p+1)|\le 2\sqrt{p}$; the hypothesis is non-vacuous for every prime $p$ (e.g. $N=p+1$ always satisfies it) and forces $N\ge 1$.
--
--   **Formalization Note.** Curves are Mathlib's `WeierstrassCurve (ZMod p)`; `E.IsElliptic` asserts that the discriminant is a unit, equivalently nonzero over a field. `Nat.card E.toAffine.Point` counts affine rational points together with the point at infinity, the same quantity as in the platform's `BSD.hasse_bound`. The benchmark's runtime budget and challenge-selection rule are properties of its verifier, not of the theorem, and are not formalized.
-- source:
--   Epoch AI, FrontierMath: Open Problems, 'Elliptic Curves with Prescribed Number of Points', https://epoch.ai/frontiermath/open-problems/elliptic-curve-point-count (Prompt: given prime p and N with |N-(p+1)|<2*sqrt(p), construct E/F_p with #E(F_p)=N). Mathematical content: M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197-272, https://doi.org/10.1007/BF02940746; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. ÉNS (4) 2 (1969), 521-560, Theorem 4.1, https://www.numdam.org/item/ASENS_1969_4_2_4_521_0/

import Mathlib

namespace PrescribedPointCount

theorem exists_isElliptic_natCard_point_eq (p : ℕ) [Fact p.Prime] (N : ℕ)
    (hN : |(N : ℝ) - ((p : ℝ) + 1)| < 2 * Real.sqrt (p : ℝ)) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = N := by sorry

end PrescribedPointCount
