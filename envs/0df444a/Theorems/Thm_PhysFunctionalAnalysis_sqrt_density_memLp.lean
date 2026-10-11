-- Prove2me | Theorems.Thm_PhysFunctionalAnalysis_sqrt_density_memLp
-- name    : PhysFunctionalAnalysis.sqrt_density_memLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:51:39.515552+00:00
-- url     : https://prove2.me/theorems/bdd28525-ca93-42c5-aa4d-cdab1943ba1e
-- title:
--   `PhysFunctionalAnalysis.sqrt_density_memLp` {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p) : MemLp (fun x => Real.sqrt (p x)) 2
-- statement:
--   Prove the following Lean 4 theorem from `PhysFunctionalAnalysis`.
--
--   `PhysFunctionalAnalysis.sqrt_density_memLp` {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p) : MemLp (fun x => Real.sqrt (p x)) 2 μ
--
--   Formalization note: Lean 4 identifier `PhysFunctionalAnalysis.sqrt_density_memLp`.

-- Generated from PhysFunctionalAnalysis.lean — theorem PhysFunctionalAnalysis.sqrt_density_memLp
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_ChapterA4
open PhysFunctionalAnalysis


open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

theorem PhysFunctionalAnalysis.sqrt_density_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p) :
    MemLp (fun x => Real.sqrt (p x)) 2 μ := by sorry
