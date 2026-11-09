-- Prove2me | Theorems.Thm_SongZhangKLS_lemma_4_3
-- name    : SongZhangKLS.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:34.334022+00:00
-- url     : https://prove2.me/theorems/825e82fc-6914-43b6-a794-523e63470da9
-- title:
--   Lemma 4.3 — Appell pairings: duality $K_k(\mu)=\|Q_k^\mu\|^2_{L^2_0\to HS}$ and $\sqrt{\mathrm{Var}_\mu[q]}\le\sum_k c_k(\mu)\|\mathbb E_\mu[D^kq]\|_{HS}$
-- statement:
--   Let $d\ge1$ be an integer and let $\mu$ be a probability measure on $\mathbb R^n$ with finite moments through order $2d$, that is $\int\|x\|^r\,d\mu<\infty$ for every integer $1\le r\le2d$. For every $1\le k\le d$:
--
--   1. **(a)** for $f\in L^2(\mu)$ and every symmetric $k$-tensor $T$,
--   $$\mathbb E_\mu\big[P_k^\mu[T]f\big]=\langle T,Q_k^\mu f\rangle_{HS},\qquad Q_k^\mu f=Q_k^\mu\big(f-\mathbb E_\mu[f]\big);$$
--   2. **(b)** with $L^2_0(\mu)=\{f\in L^2(\mu):\mathbb E_\mu[f]=0\}$,
--   $$K_k(\mu)=\sup_{\substack{f\in L^2_0(\mu)\\\|f\|_2\le1}}\|Q_k^\mu f\|_{HS}^2=\|Q_k^\mu\|^2_{L^2_0\to HS},$$
--   and for every finite family $f_1,\dots,f_N\in L^2(\mu)$,
--   $$\sum_{a=1}^N\|Q_k^\mu f_a\|_{HS}^2\le K_k(\mu)\sum_{a=1}^N\mathrm{Var}_\mu[f_a].$$
--
--   3. **(c)** Every polynomial $q$ of degree at most $d$ satisfies
--   $$\sqrt{\mathrm{Var}_\mu[q]}\le\sum_{k=1}^dc_k(\mu)\,\big\|\mathbb E_\mu[D^kq]\big\|_{HS}.$$
--
--   Part (b) expresses $K_k$ as a squared operator norm, which is how the stochastic-localization recursions of §4 control it; part (c) turns coefficient bounds into variance bounds for all polynomials.
--
--   **Formalization Note** $K_k$, $c_k$ and the variances lie in $[0,\infty]$. $\|f\|_2\le1$ is $\mathbb E_\mu[f^2]\le1$; the operator norm on $L^2_0$ is by definition the displayed supremum, so (b) states the supremum.
--
--   Differences from the source:
--   - generalization: ambient dimension $n\ge1$ (fixed throughout §4, p.22) → every $n\in\mathbb N$; reason: for $n=0$ a $k$-tensor with $k\ge1$ has no entries, so every Appell polynomial, pairing and $K_k$ vanishes and the statement holds; it specializes to every $n\ge1$
--   - encoding: polynomials on $\mathbb R^n$, derivative tensors $D^jq$, symmetric $k$-tensors and $\|\cdot\|_{HS}$ → `MvPolynomial (Fin n) ℝ` evaluated by `polyEval`, `iterPderiv`/`expectedDeriv` for the entries of $D^jq$ and $\mathbb E_\mu[D^jq]$, tensors as arrays $(\mathrm{Fin}\,k\to\mathrm{Fin}\,n)\to\mathbb R$ with `IsSymmetricTensor`, `hsNorm`; reason: Lean representation; polynomials over $\mathbb R$ are determined by their functions, so the same objects
--   - encoding: $\mathrm{Var}_\mu[\cdot]$ → `evariance` (variance in $[0,\infty]$); reason: Lean convention; a finite bound on `evariance` is the source's variance bound, without the junk value $0$ of the real variance outside $L^2$
--   - encoding: $K_k(\mu)$, $c_k(\mu)$ real, and $\|Q_k^\mu\|^2_{L^2_0\to HS}$ → `appellK`, `appellC` in $[0,\infty]$, and the supremum of $\|Q_k^\mu f\|_{HS}^2$ over $f\in L^2_0(\mu)$ with $\mathbb E_\mu[f^2]\le1$; reason: the operator norm is that supremum by definition; under finite moments through order $2k$ both constants are finite, so the same values
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Lemma 4.3, p.22

import Mathlib
import Definitions.Def_SongZhangKLS_appellK

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal

namespace SongZhangKLS

/-- **Lemma 4.3 (Appell pairings and variance)**, p.22, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `d ≥ 1` and let `µ` have finite moments through order `2d`. For any `1 ≤ k ≤ d`:
(a) for `f ∈ L²(µ)` and every symmetric `k`-tensor `T`, `E_µ[P_k^µ[T] f] = ⟨T, Q_k^µ f⟩_HS` and
`Q_k^µ f = Q_k^µ(f − E_µ[f])`;
(b) `K_k(µ) = sup_{f ∈ L²₀(µ), ‖f‖₂ ≤ 1} ‖Q_k^µ f‖²_HS = ‖Q_k^µ‖²_{L²₀→HS}`, and for every finite
family `f₁, …, f_N ∈ L²(µ)`, `Σ_a ‖Q_k^µ f_a‖²_HS ≤ K_k(µ) Σ_a Var_µ[f_a]`.
(c) Every polynomial `q` of degree at most `d` satisfies
`√Var_µ[q] ≤ Σ_{k=1}^{d} c_k(µ) ‖E_µ[D^k q]‖_HS`.

**Formalization Note.** `µ` is a probability measure on `ℝⁿ`. `K_k` and `c_k` are
`appellK`/`appellC` in `ℝ≥0∞`; variances are `evariance`. `L²₀(µ)` is `MemLp f 2 µ` with
`E_µ[f] = 0`, and `‖f‖₂ ≤ 1` is `E_µ[f²] ≤ 1`. The operator norm `‖Q_k^µ‖_{L²₀→HS}` is by definition
the displayed supremum, so (b) states the supremum. -/
theorem lemma_4_3 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (hd : 1 ≤ d) (hmom : HasFiniteMoments (μ : Measure (EuclideanSpace ℝ (Fin n))) (2 * d)) :
    (∀ k : ℕ, 1 ≤ k → k ≤ d →
      -- (a)
      (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
        (∀ T : (Fin k → Fin n) → ℝ, IsSymmetricTensor T →
          ∫ x, polyEval (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T) x * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) =
            hsInner T (appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) k f)) ∧
        appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) k f =
          appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) k (fun x => f x - ∫ y, f y ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      -- (b)
      appellK (μ : Measure (EuclideanSpace ℝ (Fin n))) k =
        (⨆ (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (_ : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧ ∫ x, f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = 0 ∧
            ∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ 1),
          ENNReal.ofReal (hsNorm (appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) k f) ^ 2)) ∧
      (∀ (N : ℕ) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ a, MemLp (f a) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) →
        ∑ a, ENNReal.ofReal (hsNorm (appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) k (f a)) ^ 2) ≤
          appellK (μ : Measure (EuclideanSpace ℝ (Fin n))) k * ∑ a, evariance (f a) (μ : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    -- (c)
    (∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ d →
      evariance (polyEval q) (μ : Measure (EuclideanSpace ℝ (Fin n))) ^ ((1 : ℝ) / 2) ≤
        ∑ k ∈ Finset.Icc 1 d, appellC (μ : Measure (EuclideanSpace ℝ (Fin n))) k *
          ENNReal.ofReal (hsNorm (expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) k q))) := by sorry

end SongZhangKLS
