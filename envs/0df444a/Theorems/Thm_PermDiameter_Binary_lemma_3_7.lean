-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_7
-- name    : PermDiameter.Binary.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:12:37.819724+00:00
-- url     : https://prove2.me/theorems/fe142dbe-1e60-40f2-95fa-acd7f0e6f48e
-- title:
--   Lemma 3.7 — an entry–exit word producing $g_1$ at position $1$ uses the entry with shift $x_*$ and at least $\ell(g_1,\Sigma_1)$ fillers at $x_*$
-- statement:
--   Work in Step 2 of the reduction (any admissible data). Let $(f,1)\in G_2$ be represented by a word $w\in\Gamma^*\Gamma_\triangleright\Gamma^*\Gamma_\triangleleft\Gamma^*$. If $f(1)=g_1$, then
--   $$\text{the entry in } w \text{ has shift } x_*,\qquad \#\{\text{fillers of } w \text{ at the position } x_*\}\ \ge\ \ell(g_1,\Sigma_1).$$
--   Thus a single entry and exit cannot produce the value $g_1$ at position $1$ more cheaply than a word for $g_1$ over $\Sigma_1$; this is what Proposition 3.12 exploits.
--
--   **Formalization Note.** The word is an `EntryExitWord` (fillers $u$, entry $e$, fillers $v$, exit $x$, fillers $w$) whose value is $(f,1)$; `fillersAt w x∗` counts the filler letters tagged with the position $x_*$. The length is in `ℕ∞`.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: a word as a sequence of group elements; "fillers at the position x∗" → fillers recorded as (position, generator) pairs, counting letters tagged x∗; reason: every word of the paper has such a tagging, and a letter tagged x∗ is a filler at x∗, so the tagged count is at most the paper's count
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 18, Lemma 3.7

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction

open Equiv

namespace PermDiameter.Binary

/-- **Lemma 3.7.** Let `(f, 1) ∈ G₂` be represented by a word `w ∈ Γ* Γ▷ Γ* Γ◁ Γ*`. If
`f(1) = g₁`, then the entry in `w` has shift `x∗`, and `w` contains at least `ℓ(g₁, Σ₁)` fillers
at the position `x∗`. -/
theorem lemma_3_7 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) (hw : W.EntryExitWordValid w)
    (f : Pos W.r → Perm (Omega1 d0 D.dc)) (hval : W.entryExitWordValue w = ⟨f, 1⟩)
    (hf : f 1 = D.g1) :
    w.e.t = W.xstar ∧
      wordLength (D.Sig1 : Set (Perm (Omega1 d0 D.dc))) D.g1 ≤ (W.fillersAt w W.xstar : ℕ∞) := by sorry

end PermDiameter.Binary
