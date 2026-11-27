-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__locBridge_nonempty_8ed29c2a970c
-- name    : P2M_Formalism_BasicNotions_Examples__locBridge_nonempty_8ed29c2a970c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:19:14.530981+00:00
-- url     : https://prove2.me/theorems/bf08703f-b99a-4f21-9b17-9adabb7bb207
-- title:
--   P2 M Formalism Basic Notions Examples  loc Bridge nonempty 8ed29c2a970c: P2 M Formalism Basic Notions Examples  loc Bridge nonempty 8ed29c2a970c
-- statement:
--   The P2 M Formalism Basic Notions Examples  loc Bridge nonempty 8ed29c2a970c construction uses the P2 M Formalism Basic Notions Examples  loc Bridge nonempty 8ed29c2a970c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocD.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocD.lean#L68-L76

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CovariantDegrees
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

theorem P2M_Formalism_BasicNotions_Examples__locBridge_nonempty_8ed29c2a970c (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ (j : Ω →+* Om l) (_ : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1), ∀ LL : FinExt l,
      (∀ (τ : ↥(KwF (E := E) j) →ₐ[ℚ_[l]] Om l) (x : ↥(KwF (E := E) j)), τ x ∈ LL.1) →
      ∃ B : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL), B.j = j ∧ B.LL = LL ∧ B.Kw.1 = KwF (E := E) j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«locBridge_nonempty» := P2M_Formalism_BasicNotions_Examples__locBridge_nonempty_8ed29c2a970c
