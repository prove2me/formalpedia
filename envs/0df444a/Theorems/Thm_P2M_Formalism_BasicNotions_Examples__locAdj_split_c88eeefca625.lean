-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__locAdj_split_c88eeefca625
-- name    : P2M_Formalism_BasicNotions_Examples__locAdj_split_c88eeefca625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:22.567881+00:00
-- url     : https://prove2.me/theorems/22d03386-67b9-47a8-9c4f-648de26abbec
-- title:
--   P2 M Formalism Basic Notions Examples  loc Adj split c88eeefca625: P2 M Formalism Basic Notions Examples  loc Adj split c88eeefca625
-- statement:
--   The P2 M Formalism Basic Notions Examples  loc Adj split c88eeefca625 construction uses the P2 M Formalism Basic Notions Examples  loc Adj split c88eeefca625 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L21-L27

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
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
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)

theorem P2M_Formalism_BasicNotions_Examples__locAdj_split_c88eeefca625 (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) :
    (locAdj sig G loc spl p).split.isSome ↔ Formalism.MainNotions.S.Loc.resChar p ∈ G := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«locAdj_split» := P2M_Formalism_BasicNotions_Examples__locAdj_split_c88eeefca625
