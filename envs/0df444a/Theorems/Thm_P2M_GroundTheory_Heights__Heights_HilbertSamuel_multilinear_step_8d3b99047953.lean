-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:29.671097+00:00
-- url     : https://prove2.me/theorems/a19d066b-3305-4f7a-8c6a-d194a85df4c2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step 8d3b99047953: P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step 8d3b99047953
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step 8d3b99047953 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step 8d3b99047953 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L143-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L143-L216

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953 {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m)
    (x e : K → ℤ) :
    f (fun _ => x) - f (fun _ => x - e) - ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons e fun _ : Fin d => x) =
      -∑ s ∈ Finset.univ.filter (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
        f (s.piecewise (fun _ => x) (fun _ => -e)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«multilinear_step» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953
