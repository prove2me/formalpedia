-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
-- name    : P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:39.571877+00:00
-- url     : https://prove2.me/theorems/4ea6adb2-c96a-4320-8049-25aaaaa4800a
-- title:
--   P2 M Ground Theory Group Coh     eq 9cd1eeda1d2f: P2 M Ground Theory Group Coh     eq 9cd1eeda1d2f
-- statement:
--   The P2 M Ground Theory Group Coh     eq 9cd1eeda1d2f construction uses the P2 M Ground Theory Group Coh     eq 9cd1eeda1d2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L51-L61

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
include hX

theorem P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f {p : ℕ} (z : cocycles X.X₃ p) (y : (Fin p → G) → X.X₂)
    (hy : ∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) (x : cocycles X.X₁ (p + 1))
    (hx : ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) = (inhomogeneousCochains.d X.X₂ p).hom y v) :
    δ hX p (p + 1) rfl (π X.X₃ p z) = π X.X₁ (p + 1) x := by sorry

alias «GroundTheory».«GroupCoh».«δ_π_eq» := P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
