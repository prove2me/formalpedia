-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:59.435181+00:00
-- url     : https://prove2.me/theorems/d3e94ccd-0b4d-49ab-badb-70024ab48399
-- title:
--   P2 M Formalism Basic Notions Examples  Tame exists unif 24bb7d189213: P2 M Formalism Basic Notions Examples  Tame exists unif 24bb7d189213
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame exists unif 24bb7d189213 construction uses the P2 M Formalism Basic Notions Examples  Tame exists unif 24bb7d189213 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L79-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L79-L120

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)

theorem P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213 (L : Type) [Field L] [NumberField L] (i : L →+* Ω) (p : ℕ) (hp0 : p ≠ 0)
    (hp : A.valuation (p : Ω) < 1) :
    ∃ π : L, π ≠ 0 ∧ ∀ y : L, y ≠ 0 → ∃ n : ℤ, A.valuation (i (y / π ^ n)) = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«exists_unif» := P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213
