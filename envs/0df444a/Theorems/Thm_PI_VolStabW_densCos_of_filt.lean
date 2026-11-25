-- Prove2me | Theorems.Thm_PI_VolStabW_densCos_of_filt
-- name    : PI.VolStabW.densCos_of_filt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:23.518065+00:00
-- url     : https://prove2.me/theorems/2ee4ee4a-ecc6-5474-b2ea-bce6af3ef908
-- title:
--   Vol Stab W: dens Cos of filt
-- statement:
--   The Vol Stab W construction uses the dens Cos of filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVGlue.lean#L12-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVGlue.lean#L12-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set

theorem PI.VolStabW.densCos_of_filt (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by sorry
