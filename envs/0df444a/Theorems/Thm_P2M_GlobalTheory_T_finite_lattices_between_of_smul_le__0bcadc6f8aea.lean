-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finite_lattices_between_of_smul_le__0bcadc6f8aea
-- name    : P2M_GlobalTheory_T_finite_lattices_between_of_smul_le__0bcadc6f8aea
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:52.853839+00:00
-- url     : https://prove2.me/theorems/0ee51e48-15ec-4178-b050-7422653bd042
-- title:
--   P2 M Global Theory T finite lattices between of smul le  0bcadc6f8aea: P2 M Global Theory T finite lattices between of smul le  0bcadc6f8aea
-- statement:
--   The P2 M Global Theory T finite lattices between of smul le  0bcadc6f8aea construction uses the P2 M Global Theory T finite lattices between of smul le  0bcadc6f8aea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FiniteLatticesBetweenOfSmulLeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FiniteLatticesBetweenOfSmulLeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteLatticesBetweenOfSmulLe
import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteLatticesBetweenOfSmulLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finite_lattices_between_of_smul_le__0bcadc6f8aea : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by sorry

alias «GlobalTheory».«T».«finite_lattices_between_of_smul_le'» := P2M_GlobalTheory_T_finite_lattices_between_of_smul_le__0bcadc6f8aea
