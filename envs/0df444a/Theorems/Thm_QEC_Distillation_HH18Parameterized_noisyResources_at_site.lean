-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_noisyResources_at_site
-- name    : QEC.Distillation.HH18Parameterized.noisyResources_at_site
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:34:54.469148+00:00
-- url     : https://prove2.me/theorems/3ce5b145-2f60-470b-b2ef-bc040a02606b
-- title:
--   HH18 Parameterized: noisy Resources at site
-- statement:
--   Each routed physical site is supplied with the actual one-qubit diagonal
--   `T†` resource at the selected error rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L39-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L39-L43

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.noisyResources_at_site (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (site : PhysicalSite m w) :
    noisyResources m w epsilon (resourceSiteEquiv m w site) =
      HH18NoisyInput.noisyTInvResource epsilon := by sorry
