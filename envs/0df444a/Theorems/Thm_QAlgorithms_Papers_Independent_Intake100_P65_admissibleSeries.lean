-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_admissibleSeries
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.admissibleSeries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:14:58.671233+00:00
-- url     : https://prove2.me/theorems/0ef00288-fe72-405a-8a11-2ce26772f3d8
-- title:
--   Formal generating-series characterization of admissibility
-- statement:
--   Let $R$ be a commutative unital ring with $2$ invertible and $\Omega=(\omega_a)_{a\ge0}$. Put $O(z)=\sum_{a\ge0}\omega_a z^a\in R[[z]]$. Then $\Omega$ is admissible in Definition 2.10 if and only if
--
--   $$(zO(z)+1-z/2)(zO(-z)-1-z/2)=z^2/4-1.$$
--
--   This is the source identity at infinity after $z=y^{-1}$ and is a coefficientwise formal identity.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 8, Remark 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Remark 2.11, PDF p.8, as a formal identity after z=y^{-1}.
No evaluation at a pole or convergence assertion is involved. -/
theorem admissibleSeries (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) :
    OmegaAdmissible omega ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
        (PowerSeries.X * PowerSeries.mk (fun a => (-1 : R)^a * omega a) - 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) =
      PowerSeries.C ((⅟ (2 : R))^2) * PowerSeries.X^2 - 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
