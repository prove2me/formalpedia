-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__spacesExample_Ysig_3621c39de4f7
-- name    : P2M_Formalism_BasicNotions_Examples__spacesExample_Ysig_3621c39de4f7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:34.663241+00:00
-- url     : https://prove2.me/theorems/9df667a6-5dc5-4c6a-b9f0-c924fa74e10d
-- title:
--   P2 M Formalism Basic Notions Examples  spaces Example Ysig 3621c39de4f7: P2 M Formalism Basic Notions Examples  spaces Example Ysig 3621c39de4f7
-- statement:
--   The P2 M Formalism Basic Notions Examples  spaces Example Ysig 3621c39de4f7 construction uses the P2 M Formalism Basic Notions Examples  spaces Example Ysig 3621c39de4f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L481-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L481-L488

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField
open scoped TensorProduct
open IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

theorem P2M_Formalism_BasicNotions_Examples__spacesExample_Ysig_3621c39de4f7 : ∀ j, j ≤ R0.m → ∀ τ : E →+* ℂ,
    ((spacesExample hstar cm T hT pz hpz hy).Y j).sig τ = sigYD R0 j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«spacesExample_Ysig» := P2M_Formalism_BasicNotions_Examples__spacesExample_Ysig_3621c39de4f7
