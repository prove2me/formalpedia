-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
-- name    : P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:46.130947+00:00
-- url     : https://prove2.me/theorems/7e95f64f-324f-4c65-9f2d-b0706f16f0a1
-- title:
--   P2 M Formalism Basic Notions Examples  LB exists emb 1690c8e74711: P2 M Formalism Basic Notions Examples  LB exists emb 1690c8e74711
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB exists emb 1690c8e74711 construction uses the P2 M Formalism Basic Notions Examples  LB exists emb 1690c8e74711 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L138-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L138-L152

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
variable {l} {Ω : Type} [Field Ω]

theorem P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711 [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ j : Ω →+* PadicAlgCl l, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«exists_emb» := P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
