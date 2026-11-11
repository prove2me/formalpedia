-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_5
-- name    : PermDiameter.Binary.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:12:47.424627+00:00
-- url     : https://prove2.me/theorems/7f1300ed-d3ed-47bd-bb57-2ad99e1120fb
-- title:
--   Lemma 3.5 — an element with shift $t\ne1$ supported on $F$ is a word fillers·bridge·fillers of length $\le d_1|F|+1\le d_1r+1$
-- statement:
--   Work in Step 2 of the reduction (any admissible data). Let $(f,t)\in G_2$ with $t\ne1$, and let $F\subseteq C_r$ be a set of positions such that $f(x)=1$ for all $x\notin F$ and $\{x,xt\}\cap S'\ne\varnothing$ for all $x\in F\cap I_t$. Then $(f,t)$ is represented by a word $w\in\Gamma^*\Gamma_\diamond\Gamma^*$ with
--   $$|w|\le d_1|F|+1\le d_1r+1 .$$
--   Moreover, $w$ can be chosen such that the bridge $(h,t)$ in $w$ has $h(x)=1$ for all $x\notin F$, and the fillers before and after the bridge are at positions in $F$ and in $Ft=\{xt:x\in F\}$, respectively.
--
--   Up to few fillers on both sides, bridges provide all elements with a given shift; this is the basic tool of Lemma 3.6, Lemma 3.8 and Proposition 3.9.
--
--   **Formalization Note.** `W : WreathData D` is an admissible choice of the Step 2 data over the Step 1 data `D`. The word is a `BridgeWord` (filler letters tagged with their position); its value is `fillerValue u * b * fillerValue v`.
--
--   Differences from the source:
--   - generalization: the data fixed in §3 (q, m, d_c, c from Lemma 3.2; r and the positions from Lemma 3.4; generating sets and transversals from Lemma 2.3) → every admissible choice of these data (LengthGapData, WreathData); reason: the paper's choices are admissible, so the statement specializes to the paper's
--   - encoding: stabilizer positions s_k of an enumeration ω₁, …, ω_{d₁} of Ω₁ → positions s(ω) indexed by the points; reason: s_k = s(ω_k), the same set S
--   - encoding: a word over Γ ∪ Γ⋄ as a sequence of group elements → fillers recorded as (position, local generator) pairs; reason: every tagged word represents a word of the paper with the same value and length and the same filler positions
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm, formulas kept as printed; reason: the construction and its lemmas use only the group operations, so they are the same for the opposite convention
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 17, Lemma 3.5

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction

open Equiv

namespace PermDiameter.Binary

/-- **Lemma 3.5.** Let `(f, t) ∈ G₂` with `t ≠ 1`, and let `F ⊆ C_r` be a set of positions with
`f(x) = 1` for all `x ∉ F` and `{x, x t} ∩ S' ≠ ∅` for all `x ∈ F ∩ I_t`. Then `(f, t)` is
represented by a word `w ∈ Γ* Γ⋄ Γ*` with `|w| ≤ d₁|F| + 1 ≤ d₁ r + 1`, whose bridge `(h, t)` has
`h(x) = 1` for all `x ∉ F`, and whose fillers before and after the bridge are at positions in `F`
and `F t`, respectively. -/
theorem lemma_3_5 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) (W : WreathData D)
    (p : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) (hp : p ∈ W.G2) (ht : p.t ≠ 1)
    (F : Finset (Pos W.r)) (hF : ∀ x, x ∉ F → p.f x = 1)
    (hFI : ∀ x ∈ F, x ∈ W.I p.t → x ∈ W.S' ∨ x * p.t ∈ W.S') :
    ∃ w : BridgeWord (Perm (Omega1 d0 D.dc)) (Pos W.r),
      W.BridgeWordValid w ∧ W.bridgeWordValue w = p ∧
      W.bridgeWordLength w ≤ D.d1 * F.card + 1 ∧ D.d1 * F.card + 1 ≤ D.d1 * W.r + 1 ∧
      (∀ x, x ∉ F → w.b.f x = 1) ∧
      (∀ xa ∈ w.u, xa.1 ∈ F) ∧ (∀ xa ∈ w.v, xa.1 ∈ F.image (fun x => x * p.t)) := by sorry

end PermDiameter.Binary
