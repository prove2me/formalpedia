-- Prove2me | Theorems.Thm_UpperTheory_exists_splitIdempotent_of_splitAt
-- name    : UpperTheory.exists_splitIdempotent_of_splitAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:57.782311+00:00
-- url     : https://prove2.me/theorems/5c21e31d-5f06-57be-8dea-96a6bf355611
-- title:
--   Upper Theory: exists split Idempotent of split At
-- statement:
--   The Upper Theory construction uses the exists split Idempotent of split At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ExistsSplitIdempotentOfSplitAt.lean#L106-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ExistsSplitIdempotentOfSplitAt.lean#L106-L182

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

theorem UpperTheory.exists_splitIdempotent_of_splitAt :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      letI := H.starRing; ∃ (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (α : ℤ_[p]), e * e = e ∧ e ≠ 0 ∧ e ≠ 1 ∧ e + sig p (𝓞 E) e = 1 ∧ α ^ 2 = -(H.d : ℤ_[p]) ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra ℤ_[p] O] (σ : 𝓞 E →+* O),
          (σ ∈ Emb (O := O) e ↔ σ H.rt = algebraMap ℤ_[p] O α) ∧ (σ ∈ Emb (O := O) (1 - e) ↔ σ H.rt = - algebraMap ℤ_[p] O α) := by sorry
