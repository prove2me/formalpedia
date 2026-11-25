-- Prove2me | Theorems.Thm_PI_Dv_TIW_perS
-- name    : PI.Dv.TIW.perS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:00.289748+00:00
-- url     : https://prove2.me/theorems/cd135d4b-4a21-424d-9af7-057371722d52
-- title:
--   TIW: per S
-- statement:
--   The TIW construction uses the per S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/PerS.lean#L14-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/PerS.lean#L14-L227

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.TIW.perS (T : GoodSet K G) (P0 P : Pair K G) (hM1 : M1 T P0) (s : T.S) :
    ∃ (g g' : Fin (nS T P s) → G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      (∀ j k, algebraMap (𝓞 K) K (Γ j k) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))))) ∧
      Γ.det ≠ 0 ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, (epsS P * MonoidAlgebra.of K G (g i)) * b' i * (eps P * eS T s) = eps P * eS T s := by sorry
