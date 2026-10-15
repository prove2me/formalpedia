-- Prove2me | Theorems.Thm_Plasticity_Ext_Brouwer_sperner
-- name    : Plasticity.Ext.Brouwer.sperner
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:30:40.924989+00:00
-- url     : https://prove2.me/theorems/4b5e5744-b0ca-413c-a2e9-81011bf6ae78
-- title:
--   Cubical Sperner lemma: a fully labelled small grid simplex exists
-- statement:
--   Let $L$ label the grid $\{0,\dots,p\}^n$ with numbers $0,\dots,n$ such that a point whose $k$-th coordinate is $0$ does not carry label $k$, and a point whose $k$-th coordinate is $p$ carries a label at most $k$. Then there are $n+1$ grid points $I_0,\dots,I_n$, any two within $1$ of each other in every coordinate, that carry all the labels $0,\dots,n$.
--
--   Applied to finer and finer grids, it gives Brouwer's fixed-point theorem for the cube.
-- source:
--   H. W. Kuhn, Some combinatorial lemmas in topology, IBM J. Res. Dev. 4 (1960), 518–524; ported from harfe/fixed-point-theorems-lean4 (MIT)

import Mathlib.Data.Fin.Basic

namespace Plasticity.Ext.Brouwer
theorem sperner (n p : ℕ) (L : (Fin n → Fin (p + 1)) → ℕ)
    (hL : ∀ v, L v ≤ n ∧ ∀ k : Fin n, (v k = 0 → L v ≠ k.1) ∧ (v k = Fin.last p → L v ≤ k.1)) :
    ∃ I : Fin (n + 1) → (Fin n → Fin (p + 1)),
      (∀ a b k, (I a k : ℕ) ≤ (I b k : ℕ) + 1) ∧ ∀ c ≤ n, ∃ a, L (I a) = c := by sorry
end Plasticity.Ext.Brouwer
