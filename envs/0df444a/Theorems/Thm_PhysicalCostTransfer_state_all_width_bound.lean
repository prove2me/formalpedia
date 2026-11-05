-- Prove2me | Theorems.Thm_PhysicalCostTransfer_state_all_width_bound
-- name    : PhysicalCostTransfer.state_all_width_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/8ca8176c-4b86-4ecf-be60-edd33303aaab
-- title:
--   PhysicalCostTransfer: State all width bound
-- statement:
--   Uniform state-indexed cost bound. The only physical assumptions are the per-state recurrence, uniform finite-width base bound, and child interfaces. No worst-case normalized function or supremum over states is introduced.
--
--   Conditional bounds for abstract physical state costs, assuming the stated recurrence and volume identities. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/PhysicalCostTransfer.lean#L14-L94). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/PhysicalCostTransfer.lean#L14-L94 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer
set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators

theorem PhysicalCostTransfer.state_all_width_bound {S ι : Type} (rows : List ι)
    (rank count : ι → ℕ) (m W : ℕ)
    (width : S → ℕ) (volume cost : S → ℝ)
    (child : S → (r : ι) → Fin (count r) → S)
    (p A B C γ : ℝ) (hm : 0 < m) (hW : 0 < W) (hp : 0 ≤ p)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hbudget : C ≤ A * (1 - γ))
    (hvolume : ∀ s, 0 ≤ volume s)
    (hrank : ∀ r ∈ rows, 0 < rank r) (hrankm : ∀ r ∈ rows, rank r < m)
    (hγ : γ = (rows.map (fun r => (count r : ℝ) / W * ((rank r : ℝ) / m) ^ p)).sum)
    (hγ1 : γ < 1)
    (child_width : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      width (child s r j) = rank r * (width s / m))
    (child_volume : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      volume (child s r j) = volume s / W)
    (uniform_base : ∀ s, 0 < width s → width s < m → cost s ≤ B * volume s)
    (physical_recurrence : ∀ s, m ≤ width s → cost s ≤ C * volume s +
      (rows.map (fun r => ∑ j : Fin (count r), cost (child s r j))).sum) :
    ∀ s, 0 < width s → cost s ≤ A * volume s * (width s : ℝ) ^ p := by sorry
