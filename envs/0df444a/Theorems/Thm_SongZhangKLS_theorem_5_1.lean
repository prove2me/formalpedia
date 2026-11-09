-- Prove2me | Theorems.Thm_SongZhangKLS_theorem_5_1
-- name    : SongZhangKLS.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:56.741783+00:00
-- url     : https://prove2.me/theorems/cf985508-02a5-4a29-8f19-8b2eeb6788e6
-- title:
--   Theorem 5.1 — Poincaré bound from polynomial variance estimates: $C_P(\nu)\le16(1+\epsilon)R^2\ell(d)^2\max\{1,a^{-1/(d+1)}\}$ for dyadic $d\ge2$
-- statement:
--   Let $d\nu(x)=e^{-W(x)}dx$ be a centered regular log-concave probability measure on $\mathbb R^n$ with $\mathrm{Cov}(\nu)\preceq I$, and suppose that $D^2W(x)\succeq aI$ for every $x\in\mathbb R^n$, where $a>0$. Let $c_k(\nu)=\sqrt{K_k(\nu)}/k!$. Let $0<\epsilon\le1$ and $R\ge2^{40}\epsilon^{-2}$, and let $\ell:\mathbb N\to[1,\infty)$ be any nondecreasing function such that
--   $$c_k(\nu)\le\frac{R^k\,\ell(k)^k}{(k+1)^2}\qquad\text{for every integer }k\ge1. \tag{48}$$
--   Then, for every dyadic integer $d\ge2$, that is $d=2^j$ with $j\ge1$,
--   $$C_P(\nu)\le16(1+\epsilon)\,R^2\,\ell(d)^2\max\big\{1,a^{-1/(d+1)}\big\}. \tag{49}$$
--
--   This is the paper's improvement of Klartag's Lichnerowicz-type inequality: polynomial variance bounds of high degree make the dependence on the curvature lower bound $a$ disappear as $d\to\infty$.
--
--   **Formalization Note** Regularity (Definition 3.1) is required of the same potential $W$ that gives the density. Centered means $\int x\,d\nu=0$, and $\mathrm{Cov}(\nu)\preceq I$ is $\int\langle v,x\rangle^2\,d\nu\le\|v\|^2$ for all $v$. $D^2W(x)\succeq aI$ is $a\|v\|^2\le D^2W(x)[v,v]$. $c_k$ and $C_P$ lie in $[0,\infty]$, and $a^{-1/(d+1)}$ is a real power.
--
--   Differences from the source:
--   - generalization: $\ell:\mathbb N\to[1,\infty)$ nondecreasing → $\ell:\mathbb N\to\mathbb R$ with $\ell(k)\ge1$ for $k\ge1$ and nondecreasing on $\{1,2,\dots\}$; reason: $\ell(0)$ never enters the statement; every function allowed by the source satisfies these weaker hypotheses, so the statement specializes to the source's
--   - encoding: $d\nu=e^{-W}dx$ regular (Definition 3.1), centered, $\mathrm{Cov}(\nu)\preceq I$, $D^2W\succeq aI$ → `IsRegularPotential ν W`, $\int x\,d\nu=0$, $\int\langle v,x\rangle^2d\nu\le\|v\|^2$ for all $v$, $a\|v\|^2\le D^2W(x)[v,v]$ for all $x,v$; reason: a continuous potential is determined by $\nu$, and for a centered measure the covariance quadratic form is $\int\langle v,x\rangle^2d\nu$; a regular measure has moments of every order; same hypotheses
--   - encoding: every dyadic integer $d\ge2$ → $d=2^j$ for every $j\ge1$; reason: the paper's definition of dyadic degrees (p.5)
--   - encoding: $c_k(\nu)$ and $C_P(\nu)$ real or $+\infty$ → `appellC` and `poincareConst` in $[0,\infty]$; reason: Lean convention; same values
--   - encoding: $C_P(\mu)\in[0,+\infty]$, the least $C$ in (1) with the $L^2$ requirement, $+\infty$ if no finite $C$ works → `poincareConst`: an infimum in $[0,\infty]$ over finite $C\ge0$ (empty infimum $=\infty$), with $\nabla f$ the Mathlib `gradient` and the variance `evariance`; reason: Lean convention; the variance is nonnegative so only $C\ge0$ matter, and for measures absolutely continuous with respect to Lebesgue measure the gradient of a locally Lipschitz function exists almost everywhere (Rademacher); same values
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Theorem 5.1, p.37 (eqs. (48)–(49)); dyadic degrees $d=2^j$, $j\ge1$, p.5

import Mathlib
import Definitions.Def_SongZhangKLS_poincareConst
import Definitions.Def_SongZhangKLS_IsRegular
import Definitions.Def_SongZhangKLS_appellK

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace SongZhangKLS

/-- **Theorem 5.1 (Poincaré bound from polynomial variance estimates)**, p.37, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `dν(x) = e^{−W(x)} dx` be a centered regular log-concave probability measure on `ℝⁿ` with
`Cov(ν) ⪯ I`. Suppose that `D²W(x) ⪰ aI` for every `x ∈ ℝⁿ`, where `a > 0`. Let
`c_k(ν) = √K_k(ν)/k!`. Let `0 < ϵ ≤ 1` and `R ≥ 2⁴⁰ ϵ⁻²`, and let `ℓ : ℕ → [1, ∞)` be any
nondecreasing function such that `c_k(ν) ≤ R^k ℓ(k)^k / (k + 1)²` for every integer `k ≥ 1` (48).
Then, for every dyadic integer `d ≥ 2`,
`C_P(ν) ≤ 16(1 + ϵ) R² ℓ(d)² max{1, a^{−1/(d+1)}}` (49).

**Formalization Note.** Regularity (Definition 3.1) is `IsRegularPotential ν W` for the same `W`
as in `dν = e^{−W}dx` (a continuous potential is determined by `ν`). Centered is `∫ x dν = 0`;
`Cov(ν) ⪯ I` is `∫ ⟨v, x⟩² dν ≤ ‖v‖²` for every `v` (the covariance quadratic form of a centered
measure). `D²W(x) ⪰ aI` is `a‖v‖² ≤ D²W(x)[v, v]` with the second Fréchet derivative.
`c_k = appellC` in `ℝ≥0∞` and `C_P = poincareConst`. The dyadic integers `d ≥ 2` are `d = 2^j`,
`j ≥ 1` (p.5). `ℓ` is required to be `≥ 1` and nondecreasing on `{1, 2, …}` only, its value at
`0` never entering the statement. `a^{−1/(d+1)}` is `Real.rpow`. -/
theorem theorem_5_1 {n : ℕ} (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (W : EuclideanSpace ℝ (Fin n) → ℝ)
    (hW : IsRegularPotential (ν : Measure (EuclideanSpace ℝ (Fin n))) W)
    (hcent : ∫ x, x ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) = 0)
    (hcov : ∀ v : EuclideanSpace ℝ (Fin n),
      ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2)
    (a : ℝ) (ha : 0 < a)
    (hHess : ∀ x v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ iteratedFDeriv ℝ 2 W x ![v, v])
    (ε R : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : (2 : ℝ) ^ 40 * ε ^ (-2 : ℤ) ≤ R)
    (ℓ : ℕ → ℝ) (hℓ1 : ∀ k : ℕ, 1 ≤ k → 1 ≤ ℓ k) (hℓmono : MonotoneOn ℓ (Set.Ici 1))
    (h48 : ∀ k : ℕ, 1 ≤ k →
      appellC (ν : Measure (EuclideanSpace ℝ (Fin n))) k ≤ ENNReal.ofReal (R ^ k * ℓ k ^ k / ((k : ℝ) + 1) ^ 2)) :
    ∀ j : ℕ, 1 ≤ j →
      poincareConst (ν : Measure (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (16 * (1 + ε) * R ^ 2 * ℓ (2 ^ j) ^ 2 *
          max 1 (a ^ (-(1 / ((2 : ℝ) ^ j + 1))))) := by sorry

end SongZhangKLS
