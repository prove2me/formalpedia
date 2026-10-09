-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_1_1
-- name    : RamanujanNotebooks.entry_1_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:15:36.371463+00:00
-- url     : https://prove2.me/theorems/27c930c6-c2c4-47b0-ab94-3f47e91201e9
-- title:
--   Section 1 principle: superposing two letter arrangements gives a magic square
-- statement:
--   Let $n\ge1$, let $a_1,\dots,a_n$ and $p_1,\dots,p_n$ be natural numbers and let each cell $(i,j)$ of an $n\times n$ array carry one index $\sigma(i,j)$ and one index $\tau(i,j)$ so that every index of either kind occurs exactly once in each row, each column and each of the two diagonals, and every pair $(\sigma,\tau)$ occurs in exactly one cell. Then the array with entries $a_{\sigma(i,j)}+p_{\tau(i,j)}$ has all row sums, column sums and both diagonal sums equal to $\sum a_k+\sum p_k$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1, Entry 1, p. 16.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch01_ch1AntiDiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1DiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1IsMagic
import Definitions.Def_RamanujanNotebooks_ch01_ch1IsSemiMagic

namespace RamanujanNotebooks
theorem entry_1_1 (n : ℕ) (hn : 0 < n) (a p : Fin n → ℕ) (σ τ : Fin n → Fin n → Fin n)
    (hσrow : ∀ i : Fin n, Function.Bijective (fun j : Fin n => σ i j))
    (hσcol : ∀ j : Fin n, Function.Bijective (fun i : Fin n => σ i j))
    (hσdiag : Function.Bijective (fun i : Fin n => σ i i))
    (hσanti : Function.Bijective (fun i : Fin n => σ i (Fin.rev i)))
    (hτrow : ∀ i : Fin n, Function.Bijective (fun j : Fin n => τ i j))
    (hτcol : ∀ j : Fin n, Function.Bijective (fun i : Fin n => τ i j))
    (hτdiag : Function.Bijective (fun i : Fin n => τ i i))
    (hτanti : Function.Bijective (fun i : Fin n => τ i (Fin.rev i)))
    (hpair : Function.Bijective (fun x : Fin n × Fin n => (σ x.1 x.2, τ x.1 x.2))) :
    ch1IsMagic (fun i j : Fin n => a (σ i j) + p (τ i j))
      ((∑ k : Fin n, a k) + (∑ k : Fin n, p k)) := by sorry
end RamanujanNotebooks
