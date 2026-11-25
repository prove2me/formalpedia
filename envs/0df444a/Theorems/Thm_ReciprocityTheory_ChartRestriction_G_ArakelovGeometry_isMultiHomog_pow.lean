-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_pow
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:17.102124+00:00
-- url     : https://prove2.me/theorems/70e25fd2-c867-56b3-8ee7-420b47594c58
-- title:
--   Arakelov Geometry: is Multi Homog pow
-- statement:
--   The Arakelov Geometry construction uses the is Multi Homog pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogXpow.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogXpow.lean#L29-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • c) := by sorry
