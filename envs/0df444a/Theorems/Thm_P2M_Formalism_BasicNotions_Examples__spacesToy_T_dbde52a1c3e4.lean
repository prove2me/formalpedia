-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__spacesToy_T_dbde52a1c3e4
-- name    : P2M_Formalism_BasicNotions_Examples__spacesToy_T_dbde52a1c3e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:56.588554+00:00
-- url     : https://prove2.me/theorems/88b41320-ec06-5ca0-b713-94bb5bbada72
-- title:
--   P2 M Formalism Basic Notions Examples  spaces Toy T dbde52a1c3e4: P2 M Formalism Basic Notions Examples  spaces Toy T dbde52a1c3e4
-- statement:
--   The P2 M Formalism Basic Notions Examples  spaces Toy T dbde52a1c3e4 construction uses the P2 M Formalism Basic Notions Examples  spaces Toy T dbde52a1c3e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L479-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L479-L479

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

theorem P2M_Formalism_BasicNotions_Examples__spacesToy_T_dbde52a1c3e4 : (spacesExample hstar cm T hT pz hpz hy).T = T := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«spacesToy_T» := P2M_Formalism_BasicNotions_Examples__spacesToy_T_dbde52a1c3e4
