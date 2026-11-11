-- Prove2me | Theorems.Thm_PermDiameter_Binary_proposition_3_12
-- name    : PermDiameter.Binary.proposition_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:13:17.67816+00:00
-- url     : https://prove2.me/theorems/0c6376de-629b-4319-858d-f4ac437e77d8
-- title:
--   Proposition 3.12 — in a negative instance $\ell(g_3,\Delta)>m$ and hence $\operatorname{diam}(G_3,\Delta)>m$
-- statement:
--   Work in Step 3 of the reduction (any admissible data). If $\ell(g_0,\Sigma_0)>k_0$, then
--   $$\ell(g_3,\Delta)>m\qquad\text{and, hence,}\qquad \operatorname{diam}(G_3,\Delta)>m .$$
--   This is the soundness half of the reduction of Theorem 3.1: the central target $g_3=(g_2,c_3^{2m-2})$ alone certifies a large diameter.
--
--   **Formalization Note.** Words over $\Delta$ may use inverses of the clocked generators, since $\Sigma_3^{-1}\subseteq\Delta$. Both conjuncts are stated.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), pp. 20–21, Proposition 3.12

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction
import Definitions.Def_PermDiameter_Binary_Clock

open Equiv

namespace PermDiameter.Binary

/-- **Proposition 3.12.** If `ℓ(g₀, Σ₀) > k₀`, then `ℓ(g₃, Δ) > m` and, hence,
`diam(G₃, Δ) > m`. -/
theorem proposition_3_12 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (h : (k0 : ℕ∞) < wordLength (Sig0 : Set (Perm (Fin d0))) g0) :
    (D.m : ℕ∞) < wordLength W.Delta W.g3 ∧ (D.m : ℕ∞) < diamOn W.G3 W.Delta := by sorry

end PermDiameter.Binary
