-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_ne_zero_of_not_incidence_5e2c1ccf5a9f
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_ne_zero_of_not_incidence_5e2c1ccf5a9f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:57.083672+00:00
-- url     : https://prove2.me/theorems/095ffb40-e866-4a2f-a637-4c5edcb6b1cd
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval ne zero of not incidence 5e2c1ccf5a9f: P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval ne zero of not incidence 5e2c1ccf5a9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval ne zero of not incidence 5e2c1ccf5a9f construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval ne zero of not incidence 5e2c1ccf5a9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L65-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_ne_zero_of_not_incidence_5e2c1ccf5a9f {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«aeval_ne_zero_of_not_incidence» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_ne_zero_of_not_incidence_5e2c1ccf5a9f
