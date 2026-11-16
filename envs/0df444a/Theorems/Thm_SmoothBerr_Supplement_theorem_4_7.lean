-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_4_7
-- name    : SmoothBerr.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:56:13.757432+00:00
-- url     : https://prove2.me/theorems/57c4242a-428d-4778-a8a2-27fbea5c0e3e
-- title:
--   Theorem 4.7 — polynomial approximation in $L^2(\mu)$: $\|xp-1\|_{L^2(\mu)}\le\varepsilon\|p\|_{L^2(\mu)}$ with $\deg p\le\lceil5/\varepsilon\rceil$
-- statement:
--   Fix $\varepsilon>0$. Let $\mu$ be a probability distribution on $\mathbb R$ supported on $[-1,1]$, and let $\|f\|_{L^2(\mu)}:=\bigl(\int|f(x)|^2\,d\mu(x)\bigr)^{1/2}$. There exists a polynomial $p$ of degree at most $k=\lceil5/\varepsilon\rceil$ such that
--   $$
--   \|xp-1\|_{L^2(\mu)}\ \le\ \varepsilon\,\|p\|_{L^2(\mu)}. \tag{7}
--   $$
--
--   Unlike uniform approximation of $1/x$ on $[-1,1]$, which is impossible near $0$, the weighted $L^2$ problem always has a solution of degree $O(1/\varepsilon)$, with the polynomial chosen according to $\mu$. Combined with Eq. (6), this gives the deterministic upper bound for symmetric systems in Theorem 2.3.
--
--   **Formalization Note** The measure is any Borel probability measure on $\mathbb R$ with $\mu(\mathbb R\setminus[-1,1])=0$. Inequality (7) is stated squared, with lower Lebesgue integrals in $[0,\infty]$; this is equivalent because both sides are nonnegative.
--
--   Differences from the source:
--   - encoding: ‖xp − 1‖_{L2(µ)} ≤ ε‖p‖_{L2(µ)} → ∫⁻ ofReal((x p(x) − 1)²) dµ ≤ ofReal(ε²) · ∫⁻ ofReal(p(x)²) dµ; reason: squaring both nonnegative sides; ε > 0
--   - encoding: a probability distribution supported on [−1, 1] → a probability measure µ on ℝ with µ([−1, 1]ᶜ) = 0; reason: the same distributions
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.7, p.8, Eq. (7); restated p.21

import Mathlib

open MeasureTheory Polynomial

namespace SmoothBerr.Supplement

/-- **Theorem 4.7 (Polynomial approximation in the L2 norm)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 4.7, p.8; restated p.21).

Fix `ε > 0`. Let `µ` be a probability distribution supported on `[−1, 1]` and
`‖f‖_{L2(µ)} := (∫ |f(x)|² dµ(x))^{1/2}`. There is a polynomial `p` of degree at most
`k = ⌈5/ε⌉` with `‖xp − 1‖_{L2(µ)} ≤ ε ‖p‖_{L2(µ)}` (7).

**Formalization Note** `µ` is any Borel probability measure on `ℝ` with `µ(ℝ ∖ [−1, 1]) = 0`.
Inequality (7) is stated squared, `∫ (xp(x) − 1)² dµ ≤ ε² ∫ p(x)² dµ`, with lower Lebesgue integrals
in `[0, ∞]` (equivalent: both sides are nonnegative and `ε > 0`). -/
theorem theorem_4_7 (ε : ℝ) (hε : 0 < ε) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
    ∃ p : ℝ[X], p.natDegree ≤ ⌈5 / ε⌉₊ ∧
      ∫⁻ x, ENNReal.ofReal ((x * p.eval x - 1) ^ 2) ∂μ ≤
        ENNReal.ofReal (ε ^ 2) * ∫⁻ x, ENNReal.ofReal (p.eval x ^ 2) ∂μ := by sorry

end SmoothBerr.Supplement
