-- Prove2me | Theorems.Thm_PauliMatrix_IsAnticommuting_card_le_three
-- name    : PauliMatrix.IsAnticommuting.card_le_three
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T01:18:35.934273+00:00
-- url     : https://prove2.me/theorems/cb14289b-4023-486d-8ea9-49fa95fbeef1
-- title:
--   An anticommuting family of $2\times2$ matrices has at most three members
-- statement:
--   **An anticommuting family of $2\times2$ matrices has at most three members.** For any finite index type $\iota$ with decidable equality and any anticommuting family $\tau:\iota\to M_2(\mathbb{C})$ ($\tau_a\tau_b+\tau_b\tau_a=2\delta_{ab}I_2$), the cardinality of $\iota$ is at most $3$. The Pauli matrices show the bound is sharp. This is the $2\times2$ input to the theorem that the Dirac gamma matrices need four dimensions.
--
--   **Formalization Note.** Binders: `{ι : Type*} [DecidableEq ι]`, implicit `τ`, hypothesis `hτ : IsAnticommuting τ`, instance `Fintype ι`; conclusion `Fintype.card ι ≤ 3`. Empty and singleton index types are included, and the bound holds trivially there. No nontriviality is assumed.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean`, `IsAnticommuting.card_le_three` (L112–L118). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean#L112-L118

import Mathlib
import Definitions.Def_PauliMatrix_IsAnticommuting

open Matrix

namespace PauliMatrix.IsAnticommuting

theorem card_le_three {ι : Type*} [DecidableEq ι]
    {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : IsAnticommuting τ) [Fintype ι] :
    Fintype.card ι ≤ 3 := by sorry

end PauliMatrix.IsAnticommuting
