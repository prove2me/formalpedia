-- Prove2me | Theorems.Thm_SongZhangKLS_lemma_3_5
-- name    : SongZhangKLS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:40.917743+00:00
-- url     : https://prove2.me/theorems/e48bf6b1-6982-4112-9009-187884b82a89
-- title:
--   Lemma 3.5 — differentiation lowers the Appell degree, and the Appell expansion of every polynomial
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$ with finite moments through order $s$.
--
--   1. For $1\le k\le s$, a symmetric $k$-tensor $T$ and $h\in\mathbb R^n$,
--   $$D_hP_k^\mu[T]=k\,P_{k-1}^\mu[T(h,\cdot)]. \tag{15}$$
--   2. More generally, for $0\le j\le k\le s$ and $h_1,\dots,h_j\in\mathbb R^n$,
--   $$D_{h_1}\cdots D_{h_j}P_k^\mu[T]=\frac{k!}{(k-j)!}\,P_{k-j}^\mu[T(h_1,\dots,h_j,\cdot)].$$
--   3. Every polynomial $q$ of degree at most $s$ has the expansion
--   $$q-\mathbb E_\mu[q]=\sum_{k=1}^{s}\frac1{k!}\,P_k^\mu\big[\mathbb E_\mu[D^kq]\big]. \tag{16}$$
--
--   The expansion (16) reduces the variance of an arbitrary polynomial to the variances of Appell polynomials, which is how Lemma 4.3(c) and Theorem 4.1 pass from $P_k^\mu[T]$ to all polynomials.
--
--   **Formalization Note** In (15) the degree is written $k+1$ with $k+1\le s$, and in item 2 as $j+m$ with $m=k-j$, so that tensor orders match in Lean. $T(h,\cdot)$ and $T(h_1,\dots,h_j,\cdot)$ contract the first slots. The identities are equalities of polynomials.
--
--   Differences from the source:
--   - encoding: polynomials on $\mathbb R^n$, derivative tensors $D^jq$, symmetric $k$-tensors and $\|\cdot\|_{HS}$ → `MvPolynomial (Fin n) ℝ` evaluated by `polyEval`, `iterPderiv`/`expectedDeriv` for the entries of $D^jq$ and $\mathbb E_\mu[D^jq]$, tensors as arrays $(\mathrm{Fin}\,k\to\mathrm{Fin}\,n)\to\mathbb R$ with `IsSymmetricTensor`, `hsNorm`; reason: Lean representation; polynomials over $\mathbb R$ are determined by their functions, so the same objects
--   - encoding: degrees $k$ with $1\le k\le s$, and $k-j$ with $0\le j\le k$ → degrees $k+1\le s$ in (15), and $j+m\le s$ with the lower degree $m$ in the general identity; reason: reindexing so that the tensor orders typecheck; the same range of cases
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Lemma 3.5, p.14

import Mathlib
import Definitions.Def_SongZhangKLS_appellPoly

open MeasureTheory MvPolynomial

namespace SongZhangKLS

/-- **Lemma 3.5 (Differentiation and expansion)**, p.14, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `µ` have finite moments through order `s`. For `1 ≤ k ≤ s`, a symmetric `k`-tensor `T` and
`h ∈ ℝⁿ`, `D_h P_k^µ[T] = k P_{k−1}^µ[T(h, ·)]` (15). More generally, for `0 ≤ j ≤ k` and
`h₁, …, h_j ∈ ℝⁿ`, `D_{h₁} ⋯ D_{h_j} P_k^µ[T] = k!/(k − j)! · P_{k−j}^µ[T(h₁, …, h_j, ·)]`. Every
polynomial `q` of degree at most `s` has the expansion
`q − E_µ[q] = Σ_{k=1}^{s} (1/k!) P_k^µ[E_µ[D^k q]]` (16).

**Formalization Note.** `µ` is a probability measure (the setting of §3.2). In (15) the degree
is written `k + 1` (so `1 ≤ k + 1 ≤ s`); in the general identity it is written `j + m` with
`m = k − j`, so that the tensor types match. `T(h, ·)` and `T(h₁, …, h_j, ·)` contract the first
slots. Identities are equalities of polynomials (equivalently of polynomial functions on `ℝⁿ`). -/
theorem lemma_3_5 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (s : ℕ)
    (hmom : HasFiniteMoments (μ : Measure (EuclideanSpace ℝ (Fin n))) s) :
    (∀ k : ℕ, k + 1 ≤ s → ∀ T : (Fin (k + 1) → Fin n) → ℝ, IsSymmetricTensor T →
      ∀ h : EuclideanSpace ℝ (Fin n),
        dirDeriv h (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) (k + 1) T) =
          C ((k + 1 : ℕ) : ℝ) * appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k (contractOne h T)) ∧
    (∀ j m : ℕ, j + m ≤ s → ∀ T : (Fin (j + m) → Fin n) → ℝ, IsSymmetricTensor T →
      ∀ h : Fin j → EuclideanSpace ℝ (Fin n),
        iterDirDeriv h (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) (j + m) T) =
          C ((Nat.factorial (j + m) : ℝ) / (Nat.factorial m : ℝ)) *
            appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) m (contractFirst h T)) ∧
    (∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ s →
      q - C (∫ x, polyEval q x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ k ∈ Finset.Icc 1 s, C ((Nat.factorial k : ℝ)⁻¹) *
          appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k (expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) k q)) := by sorry

end SongZhangKLS
