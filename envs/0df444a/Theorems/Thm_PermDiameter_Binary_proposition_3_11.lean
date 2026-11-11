-- Prove2me | Theorems.Thm_PermDiameter_Binary_proposition_3_11
-- name    : PermDiameter.Binary.proposition_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:13:26.987028+00:00
-- url     : https://prove2.me/theorems/0eea8697-7556-4cc1-a025-c86d8543b81d
-- title:
--   Proposition 3.11 — in a positive instance $\operatorname{diam}(G_3,\Delta)\le m$
-- statement:
--   Work in Step 3 of the reduction (any admissible data). If $\ell(g_0,\Sigma_0)\le k_0$, then
--   $$\operatorname{diam}(G_3,\Delta)\le m .$$
--   This is the completeness half of the reduction of Theorem 3.1: positive instances of Binary Length are mapped to positive instances of Binary Diameter.
--
--   **Formalization Note.** $\operatorname{diam}(G_3,\Delta)$ is `diamOn G3 Δ`, the supremum over $G_3$ of the lengths over $\Delta$ (inverses are in $\Delta$ by construction).
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 20, Proposition 3.11

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction
import Definitions.Def_PermDiameter_Binary_Clock

open Equiv

namespace PermDiameter.Binary

/-- **Proposition 3.11.** If `ℓ(g₀, Σ₀) ≤ k₀`, then `diam(G₃, Δ) ≤ m`. -/
theorem proposition_3_11 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (h : wordLength (Sig0 : Set (Perm (Fin d0))) g0 ≤ (k0 : ℕ∞)) :
    diamOn W.G3 W.Delta ≤ (D.m : ℕ∞) := by sorry

end PermDiameter.Binary
