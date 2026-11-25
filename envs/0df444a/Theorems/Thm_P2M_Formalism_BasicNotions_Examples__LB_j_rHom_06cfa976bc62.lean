-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
-- name    : P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:31:59.214086+00:00
-- url     : https://prove2.me/theorems/f9aab20d-9239-57fe-901f-c3a0290c6acf
-- title:
--   P2 M Formalism Basic Notions Examples  LB j r Hom 06cfa976bc62: P2 M Formalism Basic Notions Examples  LB j r Hom 06cfa976bc62
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB j r Hom 06cfa976bc62 construction uses the P2 M Formalism Basic Notions Examples  LB j r Hom 06cfa976bc62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L74-L75

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
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
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62 (σ : ↥(KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j ((rHom hj σ : G E Ω) x) = (σ : GQ l) (j x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«j_rHom» := P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
