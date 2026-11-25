-- Prove2me | Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344
-- name    : P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:06.687703+00:00
-- url     : https://prove2.me/theorems/13bc95ad-c2e8-43c8-b094-c9157f72c542
-- title:
--   P2 M Formalism Wach Cohomology Facts PCoh f D   83e0ac9c2344: P2 M Formalism Wach Cohomology Facts PCoh f D   83e0ac9c2344
-- statement:
--   The P2 M Formalism Wach Cohomology Facts PCoh f D   83e0ac9c2344 construction uses the P2 M Formalism Wach Cohomology Facts PCoh f D   83e0ac9c2344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L38-L40

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PCoh
open Formalism.WachCohomologyFacts
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
  {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)

theorem P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344 (x : ZMod n → V₁) : h.fD (W₁.Φ x) = W₂.Φ (h.fD x) := by sorry

alias «Formalism».«WachCohomologyFacts».«PCoh».«fD_Φ» := P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344
