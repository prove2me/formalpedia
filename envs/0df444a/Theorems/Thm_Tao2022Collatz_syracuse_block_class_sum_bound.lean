-- Prove2me | Theorems.Thm_Tao2022Collatz_syracuse_block_class_sum_bound
-- name    : Tao2022Collatz.syracuse_block_class_sum_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:47:28.881122+00:00
-- url     : https://prove2.me/theorems/343345dc-26e2-43ce-b4de-5c7506e6d7ee
-- title:
--   Harmonic mass of a Syracuse valuation block in one residue class (Tao, Lemma 5.3, one block)
-- statement:
--   Let $\mathrm{Syr}$ be the Syracuse map and $a(M)=\nu_2(3M+1)$. Let $x>0$, $m\ge 1$, $k\ge 0$, $b=(b_1,\dots,b_m)\in\mathbb{N}^m$ with $4\cdot 3^{k+m}\,2^{b_m}\le x$, and let $S$ be a finite set of natural numbers, pairwise congruent modulo $3^k$, such that every $M\in S$ has first $m$ Syracuse valuations $a(\mathrm{Syr}^{i}M)=b_{i+1}$ ($0\le i<m$) and satisfies $\mathrm{Syr}^{m}(M)\le x<\mathrm{Syr}^{m-1}(M)$. Then
--   $$3^k\sum_{M\in S}\frac1M\;\le\;2^{-(b_1+\dots+b_m)}\,(2+b_m).$$
--
--   Role: this is the one-valuation-block case of Tao's Lemma 5.3 (the bound $c_n(X)\ll 1$ for the residue-class harmonic sums in Section 5): a block of starting points with prescribed valuations and first passage below $x$ at step $m$ has harmonic mass, per residue class modulo $3^k$, at most $2^{-|b|}(2+b_m)$. The parent's Section 5 argument sums it over blocks.
--
--   **Formalization Note**: the valuation vector is written with `Nat.factorization 2`; the congruence is stated over $\mathbb{Z}$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 5, Lemma 5.3 (the bound $c_n(X)\ll 1$ for the residue-class harmonic sums (5.25)), one valuation block. https://arxiv.org/abs/1909.03562

import Mathlib
import Definitions.Def_syracuseStep

namespace Tao2022Collatz

theorem syracuse_block_class_sum_bound :
    ∀ (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, (fun i : Fin m => (3 * syracuseStep^[(i : ℕ)] M + 1).factorization 2) = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M),
    (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ (∑ i, b i) * (2 + b ⟨m - 1, by omega⟩) := by sorry

end Tao2022Collatz
