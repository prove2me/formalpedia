-- Prove2me | Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_key
-- name    : PositivityTheory.CW.FormEigenMonotone.key
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:25.919436+00:00
-- url     : https://prove2.me/theorems/151dbb22-ba78-4ad9-9f48-356f2bc01ff4
-- title:
--   Form Eigen Monotone: key
-- statement:
--   The Form Eigen Monotone construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L76-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L76-L124

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

theorem PositivityTheory.CW.FormEigenMonotone.key {κ c x₀ R : ℝ} {s : ℕ}
    (hA0 : ∀ w, ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1)
    (hA12 : ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
      ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re)
    (hc : 0 ≤ c) (hR : 0 < R) (ν : ℝ) (hν : 0 ≤ ν) (h : V) (hh : Eig ε E ν h) :
    phiR s R ν * (ν - κ + c) * ‖h‖ ^ 2 - (if ν < x₀ then x₀ + |κ| + c else 0) * ‖h‖ ^ 2 ≤
      (beta ε E (fc b μ (phiR s R)) h h).re := by sorry
