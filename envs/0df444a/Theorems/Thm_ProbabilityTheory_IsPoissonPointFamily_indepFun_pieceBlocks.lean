-- Prove2me | Theorems.Thm_ProbabilityTheory_IsPoissonPointFamily_indepFun_pieceBlocks
-- name    : ProbabilityTheory.IsPoissonPointFamily.indepFun_pieceBlocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:05:05.469371+00:00
-- url     : https://prove2.me/theorems/33d18912-e461-4dcb-9a1b-63d0718466e7
-- title:
--   LeanLevy: ProbabilityTheory.IsPoissonPointFamily.indepFun_pieceBlocks
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The original mathematical assertion is retained with explicit names and source-compatible universe declarations. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L397

import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : MeasureTheory.Measure E} [SigmaFinite m] [Nonempty E] {μ : MeasureTheory.Measure Ω}
private def pointFamilyBlock : ℕ ⊕ ℕ × ℕ → ℕ := Sum.elim id Prod.fst

theorem ProbabilityTheory.IsPoissonPointFamily.indepFun_pieceBlocks [MeasureTheory.IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (n : ℕ) :
    IndepFun
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n}) => pointFamilyCombined K X i.1 ω)
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1}) => pointFamilyCombined K X i.1 ω)
      μ := by sorry
