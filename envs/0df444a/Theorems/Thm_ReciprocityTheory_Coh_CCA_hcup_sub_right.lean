-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_hcup_sub_right
-- name    : ReciprocityTheory.Coh.CCA.hcup_sub_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:15.490968+00:00
-- url     : https://prove2.me/theorems/53d3a93c-ecd0-5b09-8885-c9047e4a3d58
-- title:
--   CCA: hcup sub right
-- statement:
--   The CCA construction uses the hcup sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L212-L217

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]

theorem ReciprocityTheory.Coh.CCA.hcup_sub_right {X V W Z : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F₁ F₂ : (Fin (q + 1) → X) → W) :
    hcup β p q F (F₁ - F₂) = hcup β p q F F₁ - hcup β p q F F₂ := by sorry
