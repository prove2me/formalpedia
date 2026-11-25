-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2
-- name    : P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:39.027477+00:00
-- url     : https://prove2.me/theorems/bfa8d704-1a75-4da8-9756-fb49254f9e27
-- title:
--   P2 M Formalism Basic Notions Examples  Gat R is Adic Complete e5d83f2ed8a2: P2 M Formalism Basic Notions Examples  Gat R is Adic Complete e5d83f2ed8a2
-- statement:
--   The P2 M Formalism Basic Notions Examples  Gat R is Adic Complete e5d83f2ed8a2 construction uses the P2 M Formalism Basic Notions Examples  Gat R is Adic Complete e5d83f2ed8a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatRing.lean#L116-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatRing.lean#L116-L146

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.GatR
open QuadraticAlgebra IsLocalRing
variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}

theorem P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2 (hϖ : Irreducible ϖ) (hC : IsAdicComplete (Ideal.span {ϖ}) W) :
    haveI := isDomain hϖ; haveI := isDVR hϖ
    IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«GatR».«isAdicComplete» := P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2
