-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_8
-- name    : PermDiameter.Binary.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:12:23.109913+00:00
-- url     : https://prove2.me/theorems/3f9e6ef0-ea2d-427a-afbe-bbe07fdae72e
-- title:
--   Lemma 3.8 — entry–exit words of length $\le d_1(r-1)+\ell(g'',\Lambda_y)+\ell(g''',\Lambda_t)+2$ for elements with shift $yz^{-1}$
-- statement:
--   Work in Step 2 of the reduction (any admissible data). Let $(f,t)\in G_2$ with $t=yz^{-1}$ for some $y,z\in S\setminus\{1\}$. Suppose that $f(1)\in LT_y\,g''g'''$ for some $g''\in H_y$ and $g'''\in H_t$ (where $t$ is also regarded as a position), and, in the case $y\in S'$, additionally $f(1)\notin g_1H_y\,g'''$. Then $(f,t)$ is represented by a word $w\in\Gamma^*\Gamma_\triangleright\Gamma^*\Gamma_\triangleleft\Gamma^*$ of length
--   $$|w|\le d_1(r-1)+\ell(g'',\Lambda_y)+\ell(g''',\Lambda_t)+2 .$$
--   Such words produce arbitrary values at all positions other than $1$, while the value at $1$ is controlled by the entry and by fillers at two positions; Proposition 3.9 applies this case by case.
--
--   **Formalization Note.** $f(1)\in LT_y g''g'''$ is $\exists l\in LT_y,\ f(1)=l\,g''g'''$; $f(1)\notin g_1H_yg'''$ is $f(1)\ne g_1hg'''$ for all $h\in H_y$. The bound is in `ℕ∞` (lengths are `wordLength`); $r\ge1$, so $r-1$ does not truncate.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration of Ω₁ → positions s(ω) indexed by the points; reason: the same set S
--   - encoding: a word over Σ₂ as a sequence of group elements → fillers recorded as (position, generator) pairs; reason: a tagged word represents a word of the paper with the same value and length
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: only the group operations are used
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), pp. 18–19, Lemma 3.8

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction

open Equiv

namespace PermDiameter.Binary

/-- **Lemma 3.8.** Let `(f, t) ∈ G₂` with `t = y z⁻¹` for some `y, z ∈ S ∖ {1}`. Suppose that
`f(1) ∈ LT_y g'' g'''` for some `g'' ∈ H_y` and `g''' ∈ H_t` (`t` regarded as a position), and, if
`y ∈ S'`, additionally `f(1) ∉ g₁ H_y g'''`. Then `(f, t)` is represented by a word
`w ∈ Γ* Γ▷ Γ* Γ◁ Γ*` with `|w| ≤ d₁(r − 1) + ℓ(g'', Λ_y) + ℓ(g''', Λ_t) + 2`. -/
theorem lemma_3_8 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (p : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) (hp : p ∈ W.G2)
    (y z : Pos W.r) (hy : y ∈ W.S) (hy1 : y ≠ 1) (hz : z ∈ W.S) (hz1 : z ≠ 1)
    (ht : p.t = y * z⁻¹) (g'' g''' : Perm (Omega1 d0 D.dc))
    (hg'' : g'' ∈ W.H y) (hg''' : g''' ∈ W.H p.t)
    (hf1 : ∃ l ∈ W.LT y, p.f 1 = l * g'' * g''')
    (hf2 : y ∈ W.S' → ∀ h ∈ W.H y, p.f 1 ≠ D.g1 * h * g''') :
    ∃ w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r),
      W.EntryExitWordValid w ∧ W.entryExitWordValue w = p ∧
      (W.entryExitWordLength w : ℕ∞) ≤
        ((D.d1 * (W.r - 1) : ℕ) : ℕ∞) +
          wordLength (W.Lam y : Set (Perm (Omega1 d0 D.dc))) g'' +
          wordLength (W.Lam p.t : Set (Perm (Omega1 d0 D.dc))) g''' + 2 := by sorry

end PermDiameter.Binary
