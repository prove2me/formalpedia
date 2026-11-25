-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_tens_8da75d64bf84
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_tens_8da75d64bf84
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:30.379984+00:00
-- url     : https://prove2.me/theorems/9d5ce0e3-c9a4-4b96-971a-2e81522388ae
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S tens 8da75d64bf84: P2 M Formalism Basic Notions Examples  NZ ev S tens 8da75d64bf84
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S tens 8da75d64bf84 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S tens 8da75d64bf84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L46-L51

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
variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_tens_8da75d64bf84 (ψ : ∀ i, G i → K) (x : ∀ i, MonoidAlgebra K (G i)) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (tens x) = ∏ i, evS (ψ i) (x i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_tens» := P2M_Formalism_BasicNotions_Examples__NZ_evS_tens_8da75d64bf84
