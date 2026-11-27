-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_conj_twCent_mem_centralizer
-- name    : PositivityTheory.Rg.Tf.Loc.conj_twCent_mem_centralizer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:12.866715+00:00
-- url     : https://prove2.me/theorems/9e867640-0411-5219-9e51-8998eae451b3
-- title:
--   Loc: conj tw Cent mem centralizer
-- statement:
--   The Loc construction uses the conj tw Cent mem centralizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L95-L101

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]

theorem PositivityTheory.Rg.Tf.Loc.conj_twCent_mem_centralizer (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) {δ h c : G}
    (hN : twNorm θ ℓ δ = h * c * h⁻¹) {x : G} (hx : x ∈ twCent θ δ) :
    h⁻¹ * x * h ∈ Subgroup.centralizer ({c} : Set G) := by sorry
