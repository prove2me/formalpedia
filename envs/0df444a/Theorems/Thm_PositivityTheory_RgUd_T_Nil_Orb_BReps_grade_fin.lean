-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_fin
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_fin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:15.506815+00:00
-- url     : https://prove2.me/theorems/92766222-4383-45a2-919b-e1f8d1474d32
-- title:
--   BReps: grade fin
-- statement:
--   The BReps construction uses the grade fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L43-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L43-L87

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_fin (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ b j ∈ span k (b '' {j' | w j' = w j}))
    (hN : ∀ j, N *ᵥ b j ∈ span k (b '' {j' | w j' = w j + 1}))
    (hv : v ∈ span k (b '' {j | w j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, w j < 0 → b.repr (a *ᵥ v) j = 0) :
    (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k :=
          (gradeBasisGL b).val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * (gradeBasisGL b)⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = (gradeBasisGL b).val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by sorry
