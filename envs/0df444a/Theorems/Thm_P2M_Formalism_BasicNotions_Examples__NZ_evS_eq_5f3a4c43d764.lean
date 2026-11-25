-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:51.580331+00:00
-- url     : https://prove2.me/theorems/ffb7a9b6-d676-565c-a46b-580df9132a67
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S eq 5f3a4c43d764: P2 M Formalism Basic Notions Examples  NZ ev S eq 5f3a4c43d764
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S eq 5f3a4c43d764 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S eq 5f3a4c43d764 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L20-L22

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
variable {K : Type} [Field K]

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764 {Γ : Type} [Fintype Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : evS ψ x = ∑ g, x.coeff g * ψ g := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_eq» := P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764
