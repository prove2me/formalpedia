-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_expand
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hf_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:39.116998+00:00
-- url     : https://prove2.me/theorems/1824a572-801a-47af-acee-7afc34e08b04
-- title:
--   SA: hf expand
-- statement:
--   The SA construction uses the hf expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L144-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

theorem ReciprocityTheory.ChartRestriction.G.SA.hf_expand (x y u e : ι → R) (a b a' b' : R) :
    hf σ J (x + a • u + b • e) (y + a' • u + b' • e) =
      hf σ J x y + σ a' * hf σ J x u + σ b' * hf σ J x e
      + a * (σ (hf σ J y u) + σ a' * hf σ J u u + σ b' * hf σ J u e)
      + b * (σ (hf σ J y e) + σ a' * hf σ J e u + σ b' * hf σ J e e) := by sorry
