-- Prove2me | Theorems.Thm_PauliMatrix_IsAnticommuting_linearIndependent
-- name    : PauliMatrix.IsAnticommuting.linearIndependent
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T01:16:40.476738+00:00
-- url     : https://prove2.me/theorems/3a28548a-90c9-438a-97a6-7524c9e78913
-- title:
--   Members of an anticommuting family, together with $1$, are linearly independent
-- statement:
--   **Members of an anticommuting family, together with the identity, are linearly independent.** Let $\iota$ be a nontrivial finite type with decidable equality, and let $\tau:\iota\to M_2(\mathbb{C})$ be an anticommuting family, $\tau_a\tau_b+\tau_b\tau_a=2\delta_{ab}I_2$. Then the family indexed by $\mathrm{Option}\,\iota$ — sending the extra element to $I_2$ and each $a\in\iota$ to $\tau_a$ — is linearly independent over $\mathbb{C}$. Since $M_2(\mathbb{C})$ has dimension four, this is the structural step behind the bound of three members.
--
--   **Formalization Note.** Instance binders: `DecidableEq ι`, `Fintype ι`, `Nontrivial ι`. Nontriviality is required: a one-member family need not be traceless. The family is `fun o : Option ι => o.elim 1 τ`.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean`, `IsAnticommuting.linearIndependent` (L94–L109). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean#L94-L109

import Mathlib
import Definitions.Def_PauliMatrix_IsAnticommuting

open Matrix

namespace PauliMatrix.IsAnticommuting

theorem linearIndependent {ι : Type*} [DecidableEq ι]
    {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : IsAnticommuting τ) [Fintype ι] [Nontrivial ι] :
    LinearIndependent ℂ (fun o : Option ι => o.elim (1 : Matrix (Fin 2) (Fin 2) ℂ) τ) := by sorry

end PauliMatrix.IsAnticommuting
