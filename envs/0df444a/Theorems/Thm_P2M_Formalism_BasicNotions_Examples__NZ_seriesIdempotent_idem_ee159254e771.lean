-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:35.370289+00:00
-- url     : https://prove2.me/theorems/73e38cda-9706-483c-a228-e467cbc4b47b
-- title:
--   P2 M Formalism Basic Notions Examples  NZ series Idempotent idem ee159254e771: P2 M Formalism Basic Notions Examples  NZ series Idempotent idem ee159254e771
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ series Idempotent idem ee159254e771 construction uses the P2 M Formalism Basic Notions Examples  NZ series Idempotent idem ee159254e771 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L57-L63

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
include hidem horth

theorem P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771 : e0F N es * e0F N es = e0F N es := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«seriesIdempotent_idem» := P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771
