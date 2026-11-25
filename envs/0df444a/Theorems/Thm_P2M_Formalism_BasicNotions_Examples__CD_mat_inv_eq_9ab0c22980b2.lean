-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_mat_inv_eq_9ab0c22980b2
-- name    : P2M_Formalism_BasicNotions_Examples__CD_mat_inv_eq_9ab0c22980b2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:54.768185+00:00
-- url     : https://prove2.me/theorems/92bf4ccf-c613-47bc-aad8-230368c0735e
-- title:
--   P2 M Formalism Basic Notions Examples  CD mat inv eq 9ab0c22980b2: P2 M Formalism Basic Notions Examples  CD mat inv eq 9ab0c22980b2
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD mat inv eq 9ab0c22980b2 construction uses the P2 M Formalism Basic Notions Examples  CD mat inv eq 9ab0c22980b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean#L31-L43

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
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
open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q

theorem P2M_Formalism_BasicNotions_Examples__CD_mat_inv_eq_9ab0c22980b2 (g : Formalism.UG.Upq P Q) :
    (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) =
      J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«mat_inv_eq» := P2M_Formalism_BasicNotions_Examples__CD_mat_inv_eq_9ab0c22980b2
