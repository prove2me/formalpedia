-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_matrixAction_idempotent_ac24ce58c29b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_matrixAction_idempotent_ac24ce58c29b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:59.9696+00:00
-- url     : https://prove2.me/theorems/6e0ca058-d058-45e1-aff3-9935bfb0bdaf
-- title:
--   P2 M Formalism Basic Notions Examples  NZ matrix Action idempotent ac24ce58c29b: P2 M Formalism Basic Notions Examples  NZ matrix Action idempotent ac24ce58c29b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ matrix Action idempotent ac24ce58c29b construction uses the P2 M Formalism Basic Notions Examples  NZ matrix Action idempotent ac24ce58c29b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L111-L113

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_matrixAction_idempotent_ac24ce58c29b {A : NAut N} (X : NTypes A) (μ j) : X.onMt μ j X.e0 = X.cenMt μ j ⟨X.e0, idempotent_mem_center X⟩ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«matrixAction_idempotent» := P2M_Formalism_BasicNotions_Examples__NZ_matrixAction_idempotent_ac24ce58c29b
