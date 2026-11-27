-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_idempotent_sum_b9146ee78392
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_idempotent_sum_b9146ee78392
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:10:06.403229+00:00
-- url     : https://prove2.me/theorems/4a397fec-4ab9-58aa-aa3e-73348c178bbd
-- title:
--   P2 M Formalism Basic Notions Examples  NZ idempotent sum b9146ee78392: P2 M Formalism Basic Notions Examples  NZ idempotent sum b9146ee78392
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ idempotent sum b9146ee78392 construction uses the P2 M Formalism Basic Notions Examples  NZ idempotent sum b9146ee78392 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L103-L105

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
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
open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain
variable {R : Ranks} {H : Host R}
attribute [local instance] neZero_g fact_g Classical.propDecidable
variable {what₂ : Rows.Data R} (N : NData R H what₂)
variable {K : Type} [Field K]
variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)
variable {N}

theorem P2M_Formalism_BasicNotions_Examples__NZ_idempotent_sum_b9146ee78392 {A : NAut N} (X : NTypes A) : X.e0 * X.e0 = X.e0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«idempotent_sum» := P2M_Formalism_BasicNotions_Examples__NZ_idempotent_sum_b9146ee78392
