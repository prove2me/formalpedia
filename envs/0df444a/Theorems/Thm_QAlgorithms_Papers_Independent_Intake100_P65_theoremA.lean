-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_theoremA
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.theoremA
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:11:56.512762+00:00
-- url     : https://prove2.me/theorems/6fd5dc8d-f9e0-4fad-89ac-c516920441c8
-- title:
--   Freeness and rank of cyclotomic Nazarov–Wenzl algebras
-- statement:
--   Let $R$ be a commutative unital ring in which $2$ is invertible, let $n,r\ge1$, and let $u=(u_1,\ldots,u_r)\in R^r$. Let $\Omega=(\omega_a)_{a\ge0}$ be $u$-admissible in the integral Schur-polynomial sense, equivalently $\omega_a=q_{a+1}(u)-(-1)^rq_a(u)/2+\delta_{a0}/2$. Write $W_{r,n}(u;\Omega)$ for the presented cyclotomic Nazarov–Wenzl algebra. Then it has an $R$-basis indexed by a set of size
--
--   $$r^n(2n-1)!!.$$
--
--   Here $(2n-1)!!=\prod_{j=0}^{n-1}(2j+1)$. This gives freeness with the specified rank over arbitrary allowed ground rings.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 2, Theorem A

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Theorem A, PDF p.2: freeness of the specified rank over every allowed
commutative ring, expressed by a finite indexed module basis. -/
theorem theoremA (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (u : Fin r → R) (ha : RootAdmissible omega u) :
    Nonempty (Module.Basis (Fin (r^n * oddPairingCount n)) R
      (Cyclotomic R omega .degenerate r u n)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
