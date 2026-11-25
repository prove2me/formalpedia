-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_det_succ_schur
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.det_succ_schur
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:04.142085+00:00
-- url     : https://prove2.me/theorems/ec890477-439e-4035-9c38-0c7b197e1540
-- title:
--   Flag Gram Nonneg: det succ schur
-- statement:
--   The Flag Gram Nonneg construction uses the det succ schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/NatAddZeroFinOne.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/NatAddZeroFinOne.lean#L9-L31

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_NatAddZeroFinOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.det_succ_schur {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det) :
    Z.det = (Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z (Fin.last r) (Fin.last r) - (fun b => Z (Fin.last r) (Fin.castSucc b)) ⬝ᵥ
        ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun a => Z (Fin.castSucc a) (Fin.last r)))) := by sorry
