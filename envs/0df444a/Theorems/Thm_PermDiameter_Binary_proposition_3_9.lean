-- Prove2me | Theorems.Thm_PermDiameter_Binary_proposition_3_9
-- name    : PermDiameter.Binary.proposition_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:12:42.822855+00:00
-- url     : https://prove2.me/theorems/ba901f92-490a-49d7-996b-fca11a39eaef
-- title:
--   Proposition 3.9 — in a positive instance every element of $G_2$ has an entry–exit or single-bridge word of length $\le d_1r+k_1+2\le m$
-- statement:
--   Work in Step 2 of the reduction (any admissible data) and suppose that $\ell(g_0,\Sigma_0)\le k_0$. Then every element of $G_2$ is represented by a word
--   $$w\in\Gamma^*\Gamma_\triangleright\Gamma^*\Gamma_\triangleleft\Gamma^*\quad\text{or}\quad w\in\Gamma^*\Gamma_\diamond\Gamma^*\qquad\text{of length}\qquad |w|\le d_1r+k_1+2\le m .$$
--   This is the positive half of Step 2: short words of the two restricted shapes exist for all elements, and Proposition 3.11 equips them with clock values.
--
--   **Formalization Note.** The conclusion has two conjuncts: the word bound for every $p\in G_2$, and the numerical inequality $d_1r+k_1+2\le m$.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: a word over Σ₂ as a sequence of group elements → fillers recorded as (position, generator) pairs; reason: a tagged word represents a word of the paper with the same value and length
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 19, Proposition 3.9

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction

open Equiv

namespace PermDiameter.Binary

/-- **Proposition 3.9.** Suppose that `ℓ(g₀, Σ₀) ≤ k₀`. Then every element of `G₂` is
represented by a word `w ∈ Γ* Γ▷ Γ* Γ◁ Γ*` or `w ∈ Γ* Γ⋄ Γ*` of length `|w| ≤ d₁ r + k₁ + 2 ≤ m`. -/
theorem proposition_3_9 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (h : wordLength (Sig0 : Set (Perm (Fin d0))) g0 ≤ (k0 : ℕ∞)) :
    (∀ p ∈ W.G2,
      (∃ w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r),
          W.EntryExitWordValid w ∧ W.entryExitWordValue w = p ∧
          W.entryExitWordLength w ≤ D.d1 * W.r + D.k1 + 2) ∨
      (∃ w : BridgeWord (Perm (Omega1 d0 D.dc)) (Pos W.r),
          W.BridgeWordValid w ∧ W.bridgeWordValue w = p ∧
          W.bridgeWordLength w ≤ D.d1 * W.r + D.k1 + 2)) ∧
    D.d1 * W.r + D.k1 + 2 ≤ D.m := by sorry

end PermDiameter.Binary
