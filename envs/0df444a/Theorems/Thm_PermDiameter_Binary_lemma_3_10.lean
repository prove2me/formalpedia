-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_10
-- name    : PermDiameter.Binary.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:13:15.280952+00:00
-- url     : https://prove2.me/theorems/43655b8a-9148-47ba-938e-690f7eee2611
-- title:
--   Lemma 3.10 — the clocked generators $\Sigma_3$ and $\Delta$ generate $G_3=G_2\times C_q$
-- statement:
--   Work in Step 3 of the reduction (any admissible data). The sets $\Sigma_3$ and $\Delta=\Sigma_3\cup\Sigma_3^{-1}$ generate the group $G_3$:
--   $$\langle\Sigma_3\rangle=\langle\Delta\rangle=G_3=G_2\times C_q .$$
--   Hence the output instance $(\Delta,m)$ asks about the diameter of $G_3$ itself, and $\langle\Delta\rangle\cong((G_0\times C_{q^2})\wr C_r)\times C_q$.
--
--   **Formalization Note.** $G_3=\{(g,z): g\in G_2,\ z\in\langle c_3\rangle\}$ inside `Wreath (Perm Ω₁) (C_r) × Perm (Fin dc)`; both equalities are equalities of sets with the generated subgroups.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 20, Lemma 3.10

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction
import Definitions.Def_PermDiameter_Binary_Clock

open Equiv

namespace PermDiameter.Binary

/-- **Lemma 3.10.** The sets `Σ₃` and `Δ` generate the group `G₃ = G₂ × C_q`. -/
theorem lemma_3_10 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D) :
    (Subgroup.closure W.Sig3 : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc))) =
        W.G3 ∧
      (Subgroup.closure W.Delta :
        Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc))) = W.G3 := by sorry

end PermDiameter.Binary
