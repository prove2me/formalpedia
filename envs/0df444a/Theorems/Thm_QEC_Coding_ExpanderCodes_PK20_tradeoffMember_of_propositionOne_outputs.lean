-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_tradeoffMember_of_propositionOne_outputs
-- name    : QEC.Coding.ExpanderCodes.PK20.tradeoffMember_of_propositionOne_outputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:56.368776+00:00
-- url     : https://prove2.me/theorems/6d399cc2-f966-406c-988e-9583d854322f
-- title:
--   PK20: tradeoff Member of proposition One outputs
-- statement:
--   Finite PK20 Theorem 2 construction from two literal outputs of the sole
--   Proposition 1 premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L161-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L161-L234

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.tradeoffMember_of_propositionOne_outputs
    (q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r)))
    (hInitial : FirstFamilyMember w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hFactorForwardWeight : ∀ i : FactorBit r nc w,
      HammingWeight (PKDistance.tannerAction C (Pi.single i 1)) ≤ w)
    (hFactorTransposeWeight : ∀ i : FactorRawCheck r mc,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose C)
          (Pi.single i 1)) ≤ w)
    (hFactorExpansion :
      (PKDistance.tannerAction C).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator) :
    TradeoffMember q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator A C := by sorry
