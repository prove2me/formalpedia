-- Prove2me | Theorems.Thm_SongZhangKLS_lemma_3_4
-- name    : SongZhangKLS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:24.253545+00:00
-- url     : https://prove2.me/theorems/6c3b4f45-cd94-4357-940c-3869bdc84ee5
-- title:
--   Lemma 3.4 — centering property: $P_k^\mu[T]$ is the unique polynomial with leading part $T[x,\dots,x]$ and centered expected derivatives
-- statement:
--   Let $k\ge0$, let $\mu$ be a probability measure on $\mathbb R^n$ with finite moments through order $k$, and let $T$ be a symmetric $k$-tensor. Then $P_k^\mu[T]$ is the unique polynomial of degree at most $k$ with homogeneous part $T[x,\dots,x]$ of degree $k$ such that
--   $$\mathbb E_\mu\big[D^jP_k^\mu[T]\big]=0\quad(0\le j<k),\qquad D^kP_k^\mu[T]=k!\,T. \tag{14}$$
--   The map $T\mapsto P_k^\mu[T]$ is linear, and for $k=0$ it is the identity on constants.
--
--   This characterization is what makes the correction loop of Definition 3.3 canonical, and it drives the differentiation and expansion identities of Lemma 3.5.
--
--   **Formalization Note** $D^kP=k!\,T$ is stated entrywise ($\partial_{i_1}\cdots\partial_{i_k}P$ is the constant $k!\,T_i$). Linearity is stated for linear combinations of symmetric tensors, the domain of $P_k^\mu$. A $0$-tensor is its single entry.
--
--   Differences from the source:
--   - encoding: polynomials on $\mathbb R^n$, derivative tensors $D^jq$, symmetric $k$-tensors and $\|\cdot\|_{HS}$ → `MvPolynomial (Fin n) ℝ` evaluated by `polyEval`, `iterPderiv`/`expectedDeriv` for the entries of $D^jq$ and $\mathbb E_\mu[D^jq]$, tensors as arrays $(\mathrm{Fin}\,k\to\mathrm{Fin}\,n)\to\mathbb R$ with `IsSymmetricTensor`, `hsNorm`; reason: Lean representation; polynomials over $\mathbb R$ are determined by their functions, so the same objects
--   - encoding: $T\mapsto P_k^\mu[T]$ is linear → $P_k^\mu[aT+bS]=aP_k^\mu[T]+bP_k^\mu[S]$ for symmetric $T,S$ and real $a,b$; reason: definition of linearity on the space of symmetric tensors
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Lemma 3.4, p.13

import Mathlib
import Definitions.Def_SongZhangKLS_appellPoly

open MeasureTheory MvPolynomial

namespace SongZhangKLS

/-- **Lemma 3.4 (Centering property)**, p.13, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `k ≥ 0`, let `µ` be a probability measure on `ℝⁿ` with finite moments through order `k`,
and let `T` be a symmetric `k`-tensor. The polynomial `P_k^µ[T]` is the unique polynomial of
degree at most `k` with homogeneous part `T[x, …, x]` of degree `k` such that
`E_µ[D^j P_k^µ[T]] = 0` for `0 ≤ j < k` and `D^k P_k^µ[T] = k! T` (14). The map `T ↦ P_k^µ[T]` is
linear. For `k = 0`, it is the identity on constants.

**Formalization Note.** `D^k P = k! T` is stated entrywise: every `k`-fold partial derivative
`∂_{i₁} ⋯ ∂_{i_k} P` is the constant polynomial `k! T_i`. Linearity is stated on symmetric tensors
(the domain of `P_k^µ`). A `0`-tensor is its single entry `T(Fin.elim0)`. -/
theorem lemma_3_4 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (hmom : HasFiniteMoments (μ : Measure (EuclideanSpace ℝ (Fin n))) k) :
    (∀ T : (Fin k → Fin n) → ℝ, IsSymmetricTensor T →
      ((appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T).totalDegree ≤ k ∧
        homogeneousComponent k (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T) = tensorPoly T ∧
        (∀ j < k, expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) j (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T) = 0) ∧
        (∀ i : Fin k → Fin n,
          iterPderiv i (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T) = C ((Nat.factorial k : ℝ) * T i))) ∧
      (∀ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ k →
        homogeneousComponent k Q = tensorPoly T →
        (∀ j < k, expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) j Q = 0) →
        (∀ i : Fin k → Fin n, iterPderiv i Q = C ((Nat.factorial k : ℝ) * T i)) →
        Q = appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T)) ∧
    (∀ (T S : (Fin k → Fin n) → ℝ) (a b : ℝ), IsSymmetricTensor T → IsSymmetricTensor S →
      appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k (a • T + b • S) =
        C a * appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T + C b * appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k S) ∧
    (∀ T : (Fin 0 → Fin n) → ℝ, appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) 0 T = C (T Fin.elim0)) := by sorry

end SongZhangKLS
