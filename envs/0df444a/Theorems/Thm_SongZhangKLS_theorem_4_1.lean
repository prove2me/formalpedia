-- Prove2me | Theorems.Thm_SongZhangKLS_theorem_4_1
-- name    : SongZhangKLS.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:51.429625+00:00
-- url     : https://prove2.me/theorems/97f6fef7-f02c-4561-955e-9b25ff1f8fca
-- title:
--   Theorem 4.1 — Appell variance bound $\mathrm{Var}_\mu[P_k^\mu[T]]\le\frac{256^k(k!)^2}{64k^2}\|T\|_{HS}^2$ and $c_k(\mu)\le 16^k/(8k)$ for isotropic log-concave $\mu$
-- statement:
--   Let $\mu$ be an isotropic log-concave probability measure on $\mathbb R^n$. For every integer $k\ge1$ and every fully symmetric tensor $T\in(\mathbb R^n)^{\otimes k}$,
--   $$\mathrm{Var}_\mu\big[P_k^\mu[T]\big]\le\frac{256^k(k!)^2}{64k^2}\,\|T\|_{HS}^2. \tag{17}$$
--   Equivalently, for every $k\ge1$,
--   $$c_k(\mu)\le\frac{16^k}{8k}.$$
--   Moreover, every polynomial $q:\mathbb R^n\to\mathbb R$ of degree at most $d$ satisfies
--   $$\sqrt{\mathrm{Var}_\mu[q]}\le\sum_{k=1}^d\frac{16^k}{8k}\,\big\|\mathbb E_\mu[D^kq]\big\|_{HS}.$$
--
--   These dimension-free coefficient bounds feed the curvature comparison of Theorem 5.1 with a constant growth profile, which gives the main theorem.
--
--   **Formalization Note** The three displays are three conjuncts. Variances and $c_k$ lie in $[0,\infty]$, so each bound includes finiteness. Polynomials of degree at most $d$ are `MvPolynomial (Fin n) ℝ` of total degree at most $d$.
--
--   Differences from the source:
--   - generalization: ambient dimension $n\ge1$ (fixed throughout §4, p.22) → every $n\in\mathbb N$; reason: for $n=0$ a $k$-tensor with $k\ge1$ has no entries, so every Appell polynomial, pairing and $K_k$ vanishes and the statement holds; it specializes to every $n\ge1$
--   - encoding: log-concave: $\mu(sA+(1-s)B)\ge\mu(A)^s\mu(B)^{1-s}$ for compact $A,B$ and $0\le s\le1$ → the published `FunctionalInequalities.KLS.LogConcave` (the same inequality for $0<s<1$); reason: the endpoints $s\in\{0,1\}$ are trivial for every measure under the paper's conventions, while the literal $s=0$, $A=\emptyset$ case with the convention $0^0=1$ would exclude every measure; same class
--   - encoding: isotropic: $\int x\,d\mu=0$ and $\int x\otimes x\,d\mu=I_n$ → the published `FunctionalInequalities.KLS.Isotropic` (finite second moment, mean $0$, centered covariance operator the identity); reason: finite second moments are implicit in the source's definition; same measures
--   - encoding: polynomials on $\mathbb R^n$, derivative tensors $D^jq$, symmetric $k$-tensors and $\|\cdot\|_{HS}$ → `MvPolynomial (Fin n) ℝ` evaluated by `polyEval`, `iterPderiv`/`expectedDeriv` for the entries of $D^jq$ and $\mathbb E_\mu[D^jq]$, tensors as arrays $(\mathrm{Fin}\,k\to\mathrm{Fin}\,n)\to\mathbb R$ with `IsSymmetricTensor`, `hsNorm`; reason: Lean representation; polynomials over $\mathbb R$ are determined by their functions, so the same objects
--   - encoding: $\mathrm{Var}_\mu[\cdot]$ → `evariance` (variance in $[0,\infty]$); reason: Lean convention; a finite bound on `evariance` is the source's variance bound, without the junk value $0$ of the real variance outside $L^2$
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Theorem 4.1, p.21

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_appellK

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal

namespace SongZhangKLS

/-- **Theorem 4.1 (Polynomial variance and Appell coefficient bounds)**, p.21, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `µ` be an isotropic log-concave probability measure on `ℝⁿ`. For every integer `k ≥ 1` and
fully symmetric tensor `T ∈ (ℝⁿ)^{⊗k}`,
`Var_µ[P_k^µ[T]] ≤ 256^k (k!)² / (64k²) · ‖T‖²_HS` (17). Equivalently, `c_k(µ) ≤ 16^k/(8k)` for
every `k ≥ 1`. Moreover, every polynomial `q : ℝⁿ → ℝ` of degree at most `d` satisfies
`√Var_µ[q] ≤ Σ_{k=1}^{d} 16^k/(8k) · ‖E_µ[D^k q]‖_HS`.

**Formalization Note.** Log-concavity and isotropy are the published
`FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`. Variances are
`evariance` in `ℝ≥0∞`, so each bound also asserts finiteness. The "Equivalently" line is stated as
its own clause with `c_k = appellC`. Polynomials are `MvPolynomial (Fin n) ℝ` of total degree at
most `d`. -/
theorem theorem_4_1 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave μ)
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    (∀ k : ℕ, 1 ≤ k → ∀ T : (Fin k → Fin n) → ℝ, IsSymmetricTensor T →
      evariance (polyEval (appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) k T)) (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal ((256 : ℝ) ^ k * (Nat.factorial k : ℝ) ^ 2 / (64 * (k : ℝ) ^ 2) *
          hsNorm T ^ 2)) ∧
    (∀ k : ℕ, 1 ≤ k → appellC (μ : Measure (EuclideanSpace ℝ (Fin n))) k ≤ ENNReal.ofReal ((16 : ℝ) ^ k / (8 * k))) ∧
    (∀ (d : ℕ) (q : MvPolynomial (Fin n) ℝ), q.totalDegree ≤ d →
      evariance (polyEval q) (μ : Measure (EuclideanSpace ℝ (Fin n))) ^ ((1 : ℝ) / 2) ≤
        ENNReal.ofReal (∑ k ∈ Finset.Icc 1 d, (16 : ℝ) ^ k / (8 * k) *
          hsNorm (expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) k q))) := by sorry

end SongZhangKLS
