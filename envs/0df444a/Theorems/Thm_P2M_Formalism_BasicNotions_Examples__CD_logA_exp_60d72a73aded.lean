-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
-- name    : P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:27.358347+00:00
-- url     : https://prove2.me/theorems/10819966-a139-419b-b5cb-399c9413ccb5
-- title:
--   P2 M Formalism Basic Notions Examples  CD log A exp 60d72a73aded: P2 M Formalism Basic Notions Examples  CD log A exp 60d72a73aded
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD log A exp 60d72a73aded construction uses the P2 M Formalism Basic Notions Examples  CD log A exp 60d72a73aded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L20-L20

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«logA_exp» := P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
