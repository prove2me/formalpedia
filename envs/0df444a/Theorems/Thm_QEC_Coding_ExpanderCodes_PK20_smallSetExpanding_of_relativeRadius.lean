-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_smallSetExpanding_of_relativeRadius
-- name    : QEC.Coding.ExpanderCodes.PK20.smallSetExpanding_of_relativeRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:57.248999+00:00
-- url     : https://prove2.me/theorems/b0ec6b08-d52d-48c1-8cd2-9bfc24df9f17
-- title:
--   PK20: small Set Expanding of relative Radius
-- statement:
--   Turn the relative-radius conclusion of PK20 Proposition 1 into any
--   absolute-radius instance needed by Proposition 2.  The only extra premise is
--   the displayed arithmetic containment of Hamming balls.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L74-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L74-L89

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.smallSetExpanding_of_relativeRadius
    {F ι κ : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    {radius radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator)
    (hRadius : radiusDenominator * radius ≤
      radiusNumerator * Fintype.card ι) :
    f.SmallSetExpanding radius expansionNumerator expansionDenominator := by sorry
