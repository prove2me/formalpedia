-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_augmentation_groupConj
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.augmentation_groupConj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:07.35219+00:00
-- url     : https://prove2.me/theorems/82a2fe69-8e93-4c55-8b0f-8b17bbe7653c
-- title:
--   BE20 Balanced: augmentation group Conj
-- statement:
--   The BE20 Balanced construction uses the augmentation group Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L18-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L18-L26

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.augmentation_groupConj
    {G : Type*} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) :
    HorizontalSubsystem.augmentation (LiftedProduct.groupConj a) =
      HorizontalSubsystem.augmentation a := by sorry
