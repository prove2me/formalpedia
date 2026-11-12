-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_theorem_1_5
-- name    : RelatedSchedFPTAS796.Main.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:09.245821+00:00
-- url     : https://prove2.me/theorems/b2b94153-ed15-4626-8e73-1bfd0c891ca4
-- title:
--   Theorem 1.5 (Kneser) — $|X+Y|\ge|X+H|+|Y+H|-|H|\ge|X|+|Y|-|H|$ for $H=\mathrm{Sym}_G(X+Y)$
-- statement:
--   Let $G$ be a finite abelian group and let $X,Y\subseteq G$ be nonempty. For $S\subseteq G$ write $\mathrm{Sym}_G(S)=\{g\in G: S+g=S\}$ for its symmetry set (a subgroup of $G$), and put $H=\mathrm{Sym}_G(X+Y)$. Then
--   $$|X+Y|\ \ge\ |X+H|+|Y+H|-|H|\ \ge\ |X|+|Y|-|H|.$$
--
--   This is Kneser's theorem in the formulation of Tao and Vu with the stabilizer of the sumset as the subgroup. Iterated, it gives Corollary 6.2, the growth bound for repeated sumsets modulo a lattice on which Lemma 6.7 and Theorem 1.3 rest.
--
--   **Formalization Note** Cardinalities are `Nat.card` and both inequalities are compared in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: the two inequalities between cardinalities with a subtraction → the same inequalities in $\mathbb Z$; reason: avoids truncated natural subtraction; same statement
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.5, Theorem 1.5 (Kneser's theorem [Kne53], in the formulation of [TV06, Theorem 5.5])

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

open Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Theorem 1.5 (Kneser's theorem [Kne53])**, p.5. Let `G` be a finite abelian group and
`X, Y ⊆ G` nonempty. With `Sym_G(S) = {g ∈ G : S + g = S}` (`symG`, the stabilizer of `S` under
translation),
`|X + Y| ≥ |X + Sym_G(X + Y)| + |Y + Sym_G(X + Y)| − |Sym_G(X + Y)| ≥ |X| + |Y| − |Sym_G(X + Y)|`.
Cardinalities are `Nat.card`, compared in `ℤ`. -/
theorem theorem_1_5 {G : Type*} [AddCommGroup G] [Finite G] (X Y : Set G)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    (Nat.card ↥(X + (symG (X + Y) : Set G)) : ℤ) + Nat.card ↥(Y + (symG (X + Y) : Set G))
        - Nat.card (symG (X + Y)) ≤ Nat.card ↥(X + Y) ∧
      (Nat.card X : ℤ) + Nat.card Y - Nat.card (symG (X + Y)) ≤
        (Nat.card ↥(X + (symG (X + Y) : Set G)) : ℤ) + Nat.card ↥(Y + (symG (X + Y) : Set G))
          - Nat.card (symG (X + Y)) := by sorry

end RelatedSchedFPTAS796.Main
