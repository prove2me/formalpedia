-- Prove2me | Theorems.Thm_PI_SwBig_BigCellGProof_conjTranspose_mul_mul_monomial
-- name    : PI.SwBig.BigCellGProof.conjTranspose_mul_mul_monomial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:18.821268+00:00
-- url     : https://prove2.me/theorems/0e9e3233-0cad-4ad4-9051-42b3ddb7c361
-- title:
--   Big Cell GProof: conj Transpose mul mul monomial
-- statement:
--   The Big Cell GProof construction uses the conj Transpose mul mul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean#L87-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig

theorem PI.SwBig.BigCellGProof.conjTranspose_mul_mul_monomial {n : Type*} [Fintype n] [DecidableEq n]
    (g H : Matrix n n ℂ) (ρ : n → n) (v : n → ℂ)
    (hg : ∀ b j, g b j = if b = ρ j then v j else 0) (i j : n) :
    (gᴴ * H * g) i j = star (v i) * H (ρ i) (ρ j) * v j := by sorry
