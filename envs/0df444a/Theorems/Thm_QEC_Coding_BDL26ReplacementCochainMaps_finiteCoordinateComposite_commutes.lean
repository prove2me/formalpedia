-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_finiteCoordinateComposite_commutes
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.finiteCoordinateComposite_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:53.805441+00:00
-- url     : https://prove2.me/theorems/6e8c6825-984a-4324-a28c-0b5dc3093639
-- title:
--   BDL26 Replacement Cochain Maps: finite Coordinate Composite commutes
-- statement:
--   Finite composition preserves separately proved adjacent cochain identities.
--   This algebraic lemma does not identify a raw complex with a different presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1978-L1992
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1978-L1992

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.finiteCoordinateComposite_commutes
    {Source Target : Nat → Type}
    (sourceStep : ∀ n, Word Field (Source n) →ₗ[Field] Word Field (Source (n + 1)))
    (targetStep : ∀ n, Word Field (Target n) →ₗ[Field] Word Field (Target (n + 1)))
    (boundary : ∀ n, Word Field (Source n) →ₗ[Field] Word Field (Target n))
    (commutes : ∀ n, (boundary (n + 1)).comp (sourceStep n) =
      (targetStep n).comp (boundary n)) (n : Nat) :
    (boundary n).comp (finiteCoordinateComposite sourceStep n) =
      (finiteCoordinateComposite targetStep n).comp (boundary 0) := by sorry
