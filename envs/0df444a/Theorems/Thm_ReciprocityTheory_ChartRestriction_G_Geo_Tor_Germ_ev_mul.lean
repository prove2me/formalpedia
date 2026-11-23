-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Germ_ev_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:20.001255+00:00
-- url     : https://prove2.me/theorems/96188e32-1a80-47fc-a11e-74daae4e1876
-- title:
--   Germ: ev mul
-- statement:
--   The Germ construction uses the ev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/HasSubstEv.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/HasSubstEv.lean#L30-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_mul {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f * g) = ev a f * ev a g := by sorry
