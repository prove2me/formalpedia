-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_theorem_1_3
-- name    : RelatedSchedFPTAS796.Main.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:27.559018+00:00
-- url     : https://prove2.me/theorems/a1151141-d5ab-4a98-bf7a-6b63e84c80ac
-- title:
--   Theorem 1.3 — a rectangular progression of spacing $\det(Z)$ and sides $N_i$ in $kA$ when $k|A|\ge12\cdot3^dd^{d+2}\prod N_i$
-- statement:
--   Let $N_1,\dots,N_d$ be positive integers, write $[N]=\{0,\dots,N\}$, and let $A\subseteq[N_1]\times\dots\times[N_d]$ with $0\in A$. Suppose that $Z:=L(A)=\mathrm{span}_{\mathbb Z}(A)$ is full-dimensional and that the positive integer $k$ satisfies
--   $$k\,|A|\ \ge\ 12\cdot3^d\,d^{d+2}\prod_{i=1}^dN_i.$$
--   Then there is a vector $s\in Z$ such that
--   $$s+\Big\{\sum_{i=1}^dz_i\det(Z)\,e_i:\ z_i\in\mathbb Z,\ |z_i|\le N_i\Big\}\ \subseteq\ kA,$$
--   where $kA$ is the $k$-fold sumset and $\det(Z)$ is the determinant of $Z$.
--
--   This is the paper's additive-combinatorics theorem: a dense repeated sumset contains a rectangular arithmetic progression with a separate side length in each coordinate direction. Lemma 5.7 uses it to find the grid of a dense certificate.
--
--   **Formalization Note** $\det(Z)$ is the index of $Z$ in $\mathbb Z^d$; the progression is written pointwise as $s+(z_i\det(Z))_i$. The constant $12\cdot3^dd^{d+2}$ is exact.
--
--   Differences from the source:
--   - encoding: $Z$ full-dimensional, $\det(Z)$ → $Z$ of finite index, $\det(Z)$ its index; reason: same objects for sublattices of $\mathbb Z^d$
--   - encoding: $k$ a positive integer → $k\in\mathbb N$; reason: for $d\ge1$ the hypothesis forces $k\ge1$; for $d=0$ both sides of the conclusion are $\{0\}$
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.3, Theorem 1.3 (restated p.18; proof pp.22–23)

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Lattice

set_option autoImplicit false

open Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Theorem 1.3**, p.3 (restated p.18; proof pp.22–23). Let `N_1, …, N_d` be positive integers,
`A ⊆ [N_1] × ⋯ × [N_d]` (`[N] = {0, …, N}`) with `0 ∈ A`, such that `Z := L(A) = span_ℤ(A)` is
full-dimensional, and let `k` satisfy `k|A| ≥ 12·3^d·d^{d+2}·∏_i N_i`. Then there is `s ∈ Z` with
`s + {∑_i z_i det(Z) e_i : z_i ∈ ℤ, |z_i| ≤ N_i} ⊆ kA`. Here `det(Z)` is the index of `Z` in `ℤ^d`
and `kA` is the `k`-fold sumset. -/
theorem theorem_1_3 {d : ℕ} (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) (A : Finset (Fin d → ℤ))
    (hbox : ∀ a ∈ A, ∀ i, 0 ≤ a i ∧ a i ≤ N i) (h0 : (0 : Fin d → ℤ) ∈ A)
    (hZ : (latticeGen (A : Set (Fin d → ℤ))).FiniteIndex) (k : ℕ)
    (hk : 12 * 3 ^ d * d ^ (d + 2) * ∏ i, N i ≤ k * A.card) :
    ∃ s ∈ latticeGen (A : Set (Fin d → ℤ)), ∀ z : Fin d → ℤ, (∀ i, |z i| ≤ N i) →
      s + (fun i => z i * ((latticeGen (A : Set (Fin d → ℤ))).index : ℤ)) ∈
        k • (A : Set (Fin d → ℤ)) := by sorry

end RelatedSchedFPTAS796.Main
