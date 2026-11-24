-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_nL_sub
-- name    : PIW.AdelClassFin.DictGen.nL_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:24.919881+00:00
-- url     : https://prove2.me/theorems/2e9cafeb-cc49-4a27-a722-1f677424bd55
-- title:
--   Dict Gen: n L sub
-- statement:
--   The Dict Gen construction uses the n L sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L136-L142

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)

theorem PIW.AdelClassFin.DictGen.nL_sub (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {l : Fin I.n → I.E} (hl : l ∈ I.L) : N • l ∈ abelian₂ I x := by sorry
