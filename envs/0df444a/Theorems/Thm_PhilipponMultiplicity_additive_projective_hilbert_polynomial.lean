-- Prove2me | Theorems.Thm_PhilipponMultiplicity_additive_projective_hilbert_polynomial
-- name    : PhilipponMultiplicity.additive_projective_hilbert_polynomial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T05:14:11.605457+00:00
-- url     : https://prove2.me/theorems/946c65e2-e355-4e57-98cc-e6a75824ab38
-- title:
--   The additive projective-line chart has Hilbert polynomial n + 1
-- statement:
--   Over any infinite field $K$, the homogeneous vanishing ideal of the standard affine chart $X_0\ne0$ in $\mathbf P^1_K$ has actual quotient Hilbert polynomial $P(n)=n+1$. Consequently the projective closure of the additive-line factor has Hilbert dimension $1$. The Hilbert polynomial here is the eventual polynomial of dimensions of homogeneous pieces in the polynomial-ring quotient.
-- source:
--   Elementary monomial-basis calculation for the additive factor used in Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. Supports the actual Hilbert-dimension convention of Philippon Section 3; not an additional numbered result of either paper.

import Definitions.Def_PhilipponMultiplicity_Degree
set_option autoImplicit false
open PhilipponMultiplicity

theorem PhilipponMultiplicity.additive_projective_hilbert_polynomial (K : Type*) [Field K] [Infinite K] :
    Hilbert.hilbertPolynomial K 1 (fun _ => 1)
      ((projectiveSpace K 1).vanishingIdeal
        ((fun p : Projectivization K (Fin 2 → K) => fun _ : Fin 1 => p) ''
          {p : Projectivization K (Fin 2 → K) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1 := by sorry
