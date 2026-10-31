-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_rootAdmissibleSeries
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.rootAdmissibleSeries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:19:28.999648+00:00
-- url     : https://prove2.me/theorems/edf36e11-0fb9-47bb-9666-bb914953134b
-- title:
--   Generating-series criterion for root admissibility
-- statement:
--   Let $R$ be a commutative unital ring with $2$ invertible, $r\ge1$, $u\in R^r$, and $O(z)=\sum_{a\ge0}\omega_a z^a$. Then $\Omega$ is $u$-admissible if and only if, in $R[[z]]$,
--
--   $$(zO(z)+1-z/2)\prod_{i=1}^r(1-u_i z)=(1-(-1)^rz/2)\prod_{i=1}^r(1+u_i z).$$
--
--   This is the formal identity of Lemma 3.8 at infinity with its unit power-series denominators cleared. It allows coincident and zero roots.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 16, Lemma 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 3.8, PDF p.16, with unit formal denominators cleared after z=y^{-1}.
Repeated roots and zero roots are permitted. -/
theorem rootAdmissibleSeries (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (r : ℕ) (hr : 1 ≤ r) (roots : Fin r → R) :
    RootAdmissible omega roots ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
        PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
          (∏ i : Fin r, (1 - PowerSeries.C (roots i) * PowerSeries.X)) =
      (1 - PowerSeries.C (⅟ (2 : R) * (-1 : R)^r) * PowerSeries.X) *
        (∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
