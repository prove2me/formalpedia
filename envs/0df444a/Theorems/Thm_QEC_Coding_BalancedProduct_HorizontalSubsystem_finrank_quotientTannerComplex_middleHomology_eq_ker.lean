-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_finrank_quotientTannerComplex_middleHomology_eq_ker
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:12.212761+00:00
-- url     : https://prove2.me/theorems/6a42a984-24a9-433f-9f31-e828a27a1032
-- title:
--   Horizontal Subsystem: finrank quotient Tanner Complex middle Homology eq ker
-- statement:
--   Since the quotient Tanner complex is padded by a zero second boundary,
--   its middle homology is exactly the kernel of its Tanner boundary at the level
--   of finite dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L645-L653
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L645-L653

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker
    {G aRow aCol : Type} [Fintype G]
    [Fintype aRow] [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    Module.finrank (ZMod 2) (quotientTannerComplex A).middleHomology =
      Module.finrank (ZMod 2) (LinearMap.ker (quotientBoundary A)) := by sorry
