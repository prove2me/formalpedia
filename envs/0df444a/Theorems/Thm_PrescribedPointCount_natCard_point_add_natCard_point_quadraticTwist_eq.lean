-- Prove2me | Theorems.Thm_PrescribedPointCount_natCard_point_add_natCard_point_quadraticTwist_eq
-- name    : PrescribedPointCount.natCard_point_add_natCard_point_quadraticTwist_eq
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T19:26:06.60364+00:00
-- url     : https://prove2.me/theorems/107065d8-f863-47d9-9b34-27b158dd1a85
-- title:
--   Quadratic twist: $\#E(\mathbb{F}_p)+\#E^d(\mathbb{F}_p)=2p+2$
-- statement:
--   Let $p$ be an odd prime, let $a,b\in\mathbb{F}_p$ be such that the short Weierstrass curve $E:y^2=x^3+ax+b$ is nonsingular, and let $d\in\mathbb{F}_p$ be a quadratic nonresidue (in particular $d\neq 0$). The **quadratic twist** of $E$ by $d$, the curve $E^d:y^2=x^3+d^2ax+d^3b$, then satisfies
--
--   $$\#E(\mathbb{F}_p)+\#E^d(\mathbb{F}_p)=2p+2.$$
--
--   Equivalently, the Frobenius traces satisfy $t_{E^d}=-t_E$, where $t_E=p+1-\#E(\mathbb{F}_p)$. This identity is the sign-correction step of the complex multiplication method: a construction that produces a curve of trace $-t$ is converted into one of trace $t$ by twisting, and it reduces existence questions for prescribed traces to one sign at a time.
--
--   **Formalization Note.** Both curves are built with `WeierstrassCurve.mk 0 0 0 · ·`, i.e. $a_1=a_2=a_3=0$. Nonsingularity of the twist is not assumed: it follows from $\Delta(E^d)=d^6\,\Delta(E)$. The hypothesis `¬ IsSquare d` already excludes $d=0$, since $0$ is a square. Point counts are `Nat.card ·.toAffine.Point`, affine rational points plus the point at infinity.
-- source:
--   Wikipedia, 'Twists of elliptic curves', § Quadratic twist over finite fields, https://en.wikipedia.org/wiki/Twists_of_elliptic_curves#Quadratic_twist_over_finite_fields (statement |E(K)|+|E^d(K)|=2q+2, twist y^2=x^3+d a_2 x^2+d^2 a_4 x+d^3 a_6); textbook treatment: S. Galbraith, Mathematics of Public Key Cryptography, Cambridge University Press, 2012, Chapter 9, https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf

import Mathlib

namespace PrescribedPointCount

theorem natCard_point_add_natCard_point_quadraticTwist_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b d : ZMod p) (hd : ¬ IsSquare d)
    (hE : (WeierstrassCurve.mk 0 0 0 a b).IsElliptic) :
    Nat.card (WeierstrassCurve.mk 0 0 0 a b).toAffine.Point +
        Nat.card (WeierstrassCurve.mk 0 0 0 (d ^ 2 * a) (d ^ 3 * b)).toAffine.Point =
      2 * (p + 1) := by sorry

end PrescribedPointCount
