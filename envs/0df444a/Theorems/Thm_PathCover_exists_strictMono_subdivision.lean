-- Prove2me | Theorems.Thm_PathCover_exists_strictMono_subdivision
-- name    : PathCover.exists_strictMono_subdivision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T09:46:25.003876+00:00
-- url     : https://prove2.me/theorems/9d4e58f2-09dc-439b-8ed3-2b871b875b20
-- title:
--   A path admits a finite strictly monotone subdivision with each closed block carried into one member of an open cover
-- statement:
--   Let $X$ be a topological space and let $\{A_i\}_{i\in\iota}$ be a family of **open** subsets of $X$ whose union is all of $X$. Let $f$ be a path in $X$ from $a$ to $b$, that is, a continuous map $f:[0,1]\to X$ with $f(0)=a$ and $f(1)=b$.
--
--   Then there exist an integer $n\ge 1$, points
--
--   $$0 = t_0 < t_1 < \cdots < t_n = 1$$
--
--   of $[0,1]$, and a label $\lambda_k\in\iota$ for each $k\in\{0,\dots,n-1\}$, such that for every $k$,
--
--   $$f\bigl([t_k,\,t_{k+1}]\bigr) \;\subseteq\; A_{\lambda_k}.$$
--
--   Each block is the **closed** interval $[t_k,t_{k+1}]$, so consecutive blocks overlap at their shared endpoint and the condition at $t_k$ is imposed by both of the blocks meeting there. The partition is strictly increasing, so no block is degenerate. The requirement $n\ge 1$ is stated explicitly but follows from the rest: $n = 0$ would force $t_0 = 0$ and $t_0 = 1$ at once.
--
--   The statement is purely existential: it produces some adapted subdivision, not a canonical or minimal one, and it says nothing about how $n$ depends on $f$ or on the cover. The labels need not be distinct, and nothing forces $\lambda_k \ne \lambda_{k+1}$.
--
--   This is the finite, strictly monotone form of the standard Lebesgue-number subdivision. Mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval` gives a family indexed by $\mathbb{N}$ that is only monotone and is eventually constant, so it may repeat values and has no last index; the form here is the one most callers want, with the labels attached.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, p. 35, proof of Lemma 1.15 (first paragraph for the subdivision, second for the inserted return paths). Stated here for a general open cover and a general path, independently of that context.

import Mathlib

open scoped unitInterval

namespace PathCover

theorem exists_strictMono_subdivision {X : Type*} [TopologicalSpace X] {ι : Type*} {a b : X}
    (A : ι → Set X) (hopen : ∀ i, IsOpen (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (f : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (lab : Fin n → ι),
      0 < n ∧ StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ (k : Fin n) (s : I), s ∈ Set.Icc (t k.castSucc) (t k.succ) →
        f s ∈ A (lab k):= by
  sorry

end PathCover
