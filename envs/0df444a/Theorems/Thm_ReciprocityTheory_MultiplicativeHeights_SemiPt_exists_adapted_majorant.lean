-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_exists_adapted_majorant
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.exists_adapted_majorant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:18.904515+00:00
-- url     : https://prove2.me/theorems/b659d39b-ae13-5bda-81e8-58b5ed787654
-- title:
--   Semi Pt: exists adapted majorant
-- statement:
--   The Semi Pt construction uses the exists adapted majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegG.lean#L26-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegG.lean#L26-L133

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.exists_adapted_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ)
    (hP : P.det ≠ 0) (h2m : 2 * m ≤ r) (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g)
    (hdd : ∀ i, 0 < dd i) (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) :
    ∃ M : Majorant S, ∀ σ,
      M.H σ = ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ := by sorry
