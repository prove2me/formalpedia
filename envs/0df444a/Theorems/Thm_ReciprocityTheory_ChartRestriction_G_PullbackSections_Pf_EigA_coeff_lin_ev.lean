-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_coeff_lin_ev
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.coeff_lin_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:21.058204+00:00
-- url     : https://prove2.me/theorems/6e76ac49-b832-495d-9271-fa110a7f1036
-- title:
--   Eig A: coeff lin ev
-- statement:
--   The Eig A construction uses the coeff lin ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/FormalGroupCoeffSecondLinear.lean#L20-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/FormalGroupCoeffSecondLinear.lean#L20-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {R : Type} [CommRing R] {d : ℕ}
open Formalism.FG.SolveVAux

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.coeff_lin_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (ev a f) =
      ∑ p : Fin m × Fin d, coeff (Finsupp.single p 1) f * coeff (Finsupp.single q 1) (a p.1 p.2) := by sorry
