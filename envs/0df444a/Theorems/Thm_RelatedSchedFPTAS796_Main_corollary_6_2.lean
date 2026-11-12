-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_corollary_6_2
-- name    : RelatedSchedFPTAS796.Main.corollary_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:15.914462+00:00
-- url     : https://prove2.me/theorems/65244a18-f2ce-420c-87b9-1b588e4bb86c
-- title:
--   Corollary 6.2 — $|S\bmod\Gamma|\ge\sum_i|S_i\bmod\Gamma|-(m-1)|\mathrm{Sym}_{Z_\Gamma}(S)|$
-- statement:
--   Let $\Gamma\subseteq\mathbb Z^d$ be a full-rank lattice, let $m\ge1$ be an integer, and let $S_1,\dots,S_m\subseteq\mathbb Z^d$ be nonempty sets of vectors, $S=S_1+\dots+S_m$. Then
--   $$|S\bmod\Gamma|\ \ge\ |S_1\bmod\Gamma|+\dots+|S_m\bmod\Gamma|-(m-1)\,|\mathrm{Sym}_{Z_\Gamma}(S)|,$$
--   where $Z_\Gamma=\mathbb Z^d\bmod\Gamma$ and $\mathrm{Sym}_{Z_\Gamma}(S)$ is the symmetry set of $S\bmod\Gamma$.
--
--   The corollary is the form of Kneser's theorem used throughout §6: it bounds the number of residues that a $k$-fold sumset reaches.
--
--   **Formalization Note** The sets $S_i$ may be infinite; their residue sets are finite because $\Gamma$ has finite index. Here $m$ is a local integer, not the number of machines.
--
--   Differences from the source:
--   - encoding: a full-rank (full-dimensional) lattice, $\det(\Lambda)$ → an additive subgroup of finite index, $\det$ = its index; reason: the index of a full-rank sublattice of $\mathbb Z^d$ equals the absolute determinant of any basis; same objects
--   - encoding: the inequality with a subtraction → the inequality in $\mathbb Z$; reason: avoids truncated natural subtraction
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.19, Corollary 6.2 (proof Appendix A, p.24)

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

open Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Corollary 6.2**, p.19 (proof Appendix A, p.24). Let `Γ ⊆ ℤ^d` be a full-rank lattice
(finite index), `m ≥ 1`, and `S_1, …, S_m ⊆ ℤ^d` nonempty, `S = S_1 + ⋯ + S_m`. Then
`|S mod Γ| ≥ |S_1 mod Γ| + ⋯ + |S_m mod Γ| − (m − 1)|Sym_{Z_Γ}(S)|`. -/
theorem corollary_6_2 {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ)) (hΓ : Γ.FiniteIndex) (m : ℕ)
    (hm : 1 ≤ m) (S : Fin m → Set (Fin d → ℤ)) (hS : ∀ i, (S i).Nonempty) :
    (∑ i, (Nat.card (modL Γ (S i)) : ℤ)) - ((m : ℤ) - 1) * Nat.card (symZ Γ (∑ i, S i)) ≤
      Nat.card (modL Γ (∑ i, S i)) := by sorry

end RelatedSchedFPTAS796.Main
