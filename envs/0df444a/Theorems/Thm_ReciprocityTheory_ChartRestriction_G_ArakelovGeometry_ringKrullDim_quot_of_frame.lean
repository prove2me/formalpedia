-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_quot_of_frame
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ringKrullDim_quot_of_frame
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:38.792119+00:00
-- url     : https://prove2.me/theorems/089b2df6-594c-4b7c-9602-6efeb3a74be6
-- title:
--   Arakelov Geometry: ring Krull Dim quot of frame
-- statement:
--   The Arakelov Geometry construction uses the ring Krull Dim quot of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L124-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L124-L155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ringKrullDim_quot_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by sorry
