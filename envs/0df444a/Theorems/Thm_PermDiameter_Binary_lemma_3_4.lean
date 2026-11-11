-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_4
-- name    : PermDiameter.Binary.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:21.061464+00:00
-- url     : https://prove2.me/theorems/f0c3ed81-afd6-41bd-a0e9-cfbaad643ebe
-- title:
--   Lemma 3.4 — special positions in $C_r$, $r\le10d^3$, in time polynomial in $d$: $|S|=d+2$, $S\cap S^{-1}=\{1\}$, $|S\cap St|\le3$
-- statement:
--   Given a number $d\ge2$, one can compute in time polynomial in $d$ a number $r\le10d^3$ and positions $s_1,\dots,s_d\in C_r$ such that, for **all** distinct $i,j\in[1,d]$, the position $x_*=s_i^{-1}s_j$ and the set of special positions $S=\{1,s_1,\dots,s_d,x_*\}$ satisfy:
--
--   1. the special positions are pairwise distinct, $|S|=d+2$;
--   2. $S\cap S^{-1}=\{1\}$ and $|S\cap St|\le3$ for all $t\in C_r$ with $t\ne1$.
--
--   $$r\le10d^3,\qquad \forall i\ne j:\ |S|=d+2,\quad S\cap S^{-1}=\{1\},\quad \forall t\ne1:\ |S\cap St|\le 3 .$$
--   The positions are computed from $d$ alone; only $x_*$ depends on $i,j$. They keep the number of bridges of Step 2 polynomial.
--
--   **Formalization Note.** $C_r$ is $\mathbb Z/r\mathbb Z$ written multiplicatively; the output is $r$ and the residues $s_1,\dots,s_d\in[0,r)$ in binary, and $d$ is given in unary. $r\ge1$ is stated explicitly ($C_r$ has order $r$).
--
--   Differences from the source:
--   - encoding: "given d, in time polynomial in d"; positions in C_r; [1, d] → d in unary (subtype d ≥ 2), output (r, [s₁, …, s_d]) with residues < r, C_r = Multiplicative (ZMod r) with 0 < r, indices Fin d; reason: running time in the value of d needs a unary input; residues are the paper's own identification of C_r with ℤ_r (p. 15)
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 14, Lemma 3.4

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_Problems
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Lemma 3.4** (special positions). Given `d ≥ 2` (in unary), one can compute in time
polynomial in `d` a number `r ≤ 10 d³` and positions `s₁, …, s_d ∈ C_r` (residues `< r`) such that
for **all** distinct `i, j`, the set `S = {1, s₁, …, s_d, x∗}` with `x∗ = s_i⁻¹ s_j` satisfies
(i) `|S| = d + 2` and (ii) `S ∩ S⁻¹ = {1}` and `|S ∩ S t| ≤ 3` for all `t ≠ 1`. -/
theorem lemma_3_4 :
    ∃ F : {d : ℕ // 2 ≤ d} → ℕ × List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime (fun d => encUnary d.1) encNatAndList F) ∧
      ∀ d : {d : ℕ // 2 ≤ d},
        0 < (F d).1 ∧ (F d).1 ≤ 10 * d.1 ^ 3 ∧ (F d).2.length = d.1 ∧
        (∀ a ∈ (F d).2, a < (F d).1) ∧
        ∀ i j : Fin d.1, i ≠ j →
          SpecialPositionsProp
            (fun k : Fin d.1 => Multiplicative.ofAdd (((F d).2.getD k.val 0 : ℕ) : ZMod (F d).1))
            i j := by sorry

end PermDiameter.Binary
