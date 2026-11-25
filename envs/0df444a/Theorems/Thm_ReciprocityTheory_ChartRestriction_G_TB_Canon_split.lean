-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_split
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:20.293218+00:00
-- url     : https://prove2.me/theorems/db030f33-cf04-4012-b70e-747222c5052f
-- title:
--   Canon: split
-- statement:
--   The Canon construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L411-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L411-L494

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.split (α : PS k 3 d) (ax : ∀ {n} (y w : Q k d n), E3 α 0 y w = 0) (sym : ∀ {n} (x y w : Q k d n), E3 α x y w = E3 α y x w)
    (coc : ∀ {n} (x y t w : Q k d n), E3 α x y w + E3 α (x + y) t w = E3 α y t w + E3 α x (y + t) w) :
    ∃ H : PS k 2 d, (∀ {n} (x y w : Q k d n), E3 α x y w = E2 H x w + E2 H y w - E2 H (x + y) w) ∧
      (∀ {n} (w : Q k d n), E2 H 0 w = 0) ∧ ∀ {n} (b) (w : Q k d n), E2 (pderiv k (0, b) H) 0 w = 0 := by sorry
