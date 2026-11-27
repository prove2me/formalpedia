-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_satDeg_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.satDeg_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:55:26.496626+00:00
-- url     : https://prove2.me/theorems/c7d0b1c6-b031-5ba7-a383-db4b5e3d39aa
-- title:
--   T0: sat Deg le
-- statement:
--   The T0 construction uses the sat Deg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SatDegLe.lean#L8-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SatDegLe.lean#L8-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

theorem ReciprocityTheory.ChartRestriction.G.T0.satDeg_le (K : Type) [Field K] [NumberField K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : MvPolynomial κ K) (hF : F ≠ 0) (T S : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (F * MvPolynomial.monomial m 1).support ⊆ T) :
    ∃ b : Fin S.card → Fin r → K, (∀ j, b j ∈ stdLat K r) ∧ LinearIndependent K b ∧
      Submodule.span K (Set.range b) =
        Submodule.span K (Set.range fun m : S => fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff
          (e.symm i : κ →₀ ℕ)) ∧
      ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b) b ≤
        -((S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F) := by sorry
