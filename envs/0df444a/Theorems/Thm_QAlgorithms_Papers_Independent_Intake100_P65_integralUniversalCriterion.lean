-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_integralUniversalCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.integralUniversalCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:18:49.777813+00:00
-- url     : https://prove2.me/theorems/8724defb-56f0-45c6-a7bc-f8a06d4dd5fd
-- title:
--   Universal integral admissibility criterion
-- statement:
--   Let $r\ge1$, $R=\mathbb Z[u_1,\ldots,u_r]$ with independent indeterminates, and $K=\mathbb Q(u_1,\ldots,u_r)$. Let each $\omega_a$ be an element of $R$, with $\omega_0\ne0$. Interpret $u$-admissibility using the universal integral Schur polynomial $\eta_a$ of the accepted library. Then it is equivalent to the simultaneous assertion, for every $n\ge0$, that
--
--   $$K\otimes_R W_{r,n}(u;\Omega)\text{ is semisimple},\qquad W_{r,n}(u;\Omega)\text{ is free over }R\text{ of rank }r^n(2n-1)!!.$$
--
--   At $n=0$, $W_{r,0}=R$ and $(-1)!!=1$. This retains the integral freeness conclusion, without inverting $2$ in $R$.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 16, Remark 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Remark 3.7, PDF p.16. R is exactly Z[u], without assuming 2 is a unit
there. Printed: Z[u] conflicts with the global inverse-of-2 convention.
Changed: evaluate the integral Schur lift, equivalently the half-formula in
Q(u), because this retains the explicitly printed integral freeness claim.
The n=0 algebra
is R, and semisimplicity and freeness are asserted simultaneously for every n. -/
theorem integralUniversalCriterion (r : ℕ) (hr : 1 ≤ r)
    (omega : ℕ → MvPolynomial (Fin r) ℤ) (hzero : omega 0 ≠ 0) :
    RootAdmissible omega (fun i : Fin r => MvPolynomial.X i) ↔
      ∀ n : ℕ,
        IsSemisimpleRing
          ((FractionRing (MvPolynomial (Fin r) ℤ)) ⊗[MvPolynomial (Fin r) ℤ]
            (Cyclotomic (MvPolynomial (Fin r) ℤ) omega .degenerate r
              (fun i => MvPolynomial.X i) n)) ∧
        Nonempty (Module.Basis (Fin (r^n * oddPairingCount n))
          (MvPolynomial (Fin r) ℤ)
          (Cyclotomic (MvPolynomial (Fin r) ℤ) omega .degenerate r
            (fun i => MvPolynomial.X i) n)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
