-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:33:54.456096+00:00
-- url     : https://prove2.me/theorems/c2ee923a-ca61-423d-927b-9d4a47e5fe8f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e T coeff 364da66b02d3: P2 M Formalism Basic Notions Examples  NZ e T coeff 364da66b02d3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e T coeff 364da66b02d3 construction uses the P2 M Formalism Basic Notions Examples  NZ e T coeff 364da66b02d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L88-L88

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3 (g : Γ) : (eT K Γ).coeff g = ((Nat.card Γ : K))⁻¹ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eT_coeff» := P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
