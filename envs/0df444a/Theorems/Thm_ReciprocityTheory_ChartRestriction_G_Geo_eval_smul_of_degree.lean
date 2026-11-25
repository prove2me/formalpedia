-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_degree
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_degree
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:47.32602+00:00
-- url     : https://prove2.me/theorems/34a50a26-961b-4175-adbc-1183c568c554
-- title:
--   Geo: eval smul of degree
-- statement:
--   The Geo construction uses the eval smul of degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L81-L84

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_degree {σ : Type*} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ)
    (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (c : k) (v : σ → k) :
    eval (c • v) H = c ^ d * eval v H := by sorry
