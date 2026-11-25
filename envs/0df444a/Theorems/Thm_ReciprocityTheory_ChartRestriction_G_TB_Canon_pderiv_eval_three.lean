-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_eval_three
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_eval_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:33.980514+00:00
-- url     : https://prove2.me/theorems/b2b51674-bc04-40a1-94f3-e4a84b43d8d4
-- title:
--   Canon: pderiv eval three
-- statement:
--   The Canon construction uses the pderiv eval three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L234-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L234-L244

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

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_eval_three {j : Fin n} {u v w : Q k d n} {s t r : PS k n d} (hu : Dir j u s) (hv : Dir j v t) (hw : Dir j w r) (b : Fin d)
    (f : PS k 3 d) : pderiv k (j, b) (E3 f u v w) =
      E3 (pderiv k (0, b) f) u v w * s + E3 (pderiv k (1, b) f) u v w * t + E3 (pderiv k (2, b) f) u v w * r := by sorry
