-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_drazin_multiplication_projector
-- name    : WeierstrassEllipticZeta.drazin_multiplication_projector
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T02:06:11.593459+00:00
-- url     : https://prove2.me/theorems/c530bb79-beab-4ae1-b32a-3462c7bbc50c
-- title:
--   Canonical Fitting projector from generalized inverse relations
-- statement:
--   Let B be a commutative complex algebra, a,b in B, and d a natural number.
--   Assume a*b*b=b and a^(d+1)*b=a^d. Put f(x)=a*x and P(x)=(a*b)*x.
--   Then a*b and the complex-linear endomorphism P are idempotent,
--   ker(P)=ker(f^d), and range(P)=range(f^d). These last two subspaces are
--   complementary, and P is the linear projection onto range(f^d) along
--   ker(f^d). The statement includes d=0 and does not require B to be
--   finite dimensional or nontrivial.
--
--   For the mission, B is a polynomial contact quotient and b is its
--   already constructed unique generalized inverse. This result gives
--   an explicit formula for the associated Fitting projector.
-- source:
--   Derived algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. In a commutative complex algebra, the relations a*b*b=b and a^(d+1)*b=a^d make multiplication by a*b the canonical projection onto the image of multiplication by a^d along its kernel. The proof includes d=0 and needs no finite dimensional hypothesis. Primary Mathlib references: Algebra.lmul, IsIdempotentElem.pow_eq, LinearMap.IsIdempotentElem.isCompl and LinearMap.IsIdempotentElem.eq_projection. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projection

open scoped Classical

theorem WeierstrassEllipticZeta.drazin_multiplication_projector
    (B : Type*) [CommRing B] [Algebra ℂ B] (a b : B) (d : ℕ)
    (h₁ : a * b * b = b) (h₂ : a ^ (d + 1) * b = a ^ d) :
    let f := Algebra.lmul ℂ B a
    let P := Algebra.lmul ℂ B (a * b)
    IsIdempotentElem (a * b) ∧ IsIdempotentElem P ∧
      LinearMap.ker P = LinearMap.ker (f ^ d) ∧
      LinearMap.range P = LinearMap.range (f ^ d) ∧
      ∃ h : IsCompl (LinearMap.range (f ^ d)) (LinearMap.ker (f ^ d)),
        P = (LinearMap.range (f ^ d)).projection (LinearMap.ker (f ^ d)) h := by sorry
