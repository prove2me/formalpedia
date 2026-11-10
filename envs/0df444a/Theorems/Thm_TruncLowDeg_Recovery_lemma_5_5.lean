-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_5_5
-- name    : TruncLowDeg.Recovery.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:27.761036+00:00
-- url     : https://prove2.me/theorems/7716331f-99ea-4524-82df-92dd6edcca47
-- title:
--   Lemma 5.5 — Remez-type anti-concentration $O((d+L^2)t^{1/k})$ under a Gaussian on an ellipsoid and $O(d\,t^{1/k})$ on a cube
-- statement:
--   Let $k\ge1$, $0\ne p\in\mathbb R[x]_{\le k}$ and $t>0$. Let $\mu\in\mathbb R^d$, $\Sigma\succ0$, $L>0$ and $B=\{x:\|\Sigma^{-1/2}(x-\mu)\|_2\le L\}$. Then
--   $$\mathbb P_{X\sim\mathcal N(\mu,\Sigma)}\Big[X\in B\text{ and }|p(X)|<t\cdot\sup_{y\in B}|p(y)|\Big]\le O\big((d+L^2)\,t^{1/k}\big),$$
--   and for $\rho>0$,
--   $$\mathbb P_{X\sim\mathrm{Unif}([-\rho,\rho]^d)}\Big[|p(X)|<t\cdot\sup_{y\in[-\rho,\rho]^d}|p(y)|\Big]\le O\big(d\,t^{1/k}\big).$$
--   Both bounds say a low-degree polynomial is rarely much smaller than its maximum; they drive the lower bounds in Proposition 6.4 and Lemma 6.5 and the norm comparisons of Lemma 5.7.
--
--   **Formalization Note.** One universal constant $C$ replaces both $O(\cdot)$, fixed before $d,k,p,t,\mu,\Sigma,L,\rho$. Probabilities are measures of the events (`ENNReal.ofReal` of the bound).
--
--   Differences from the source:
--
--   - encoding: each O(·), Ω(·), Õ(·) → one explicit constant C, existentially quantified before every other variable it is uniform over; reason: the single-constant form is equivalent to separate constants (take the maximum)
--   - reading: ℝ^d with the dimension left implicit → hypothesis `1 ≤ d`; reason: the paper works in ℝ^d with d ≥ 1 (coordinates j ∈ {1, …, d}); at d = 0 the expressions d^{O(k)}, (d + L²) and d·t^{1/k} degenerate and the paper never considers it
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - encoding: Unif([−ρ, ρ]^d) and sup over B or the cube → `cubeUnif d ρ` (Lebesgue measure conditioned on the cube) and `supAbs` (sSup of |p| over the compact set); reason: the definitions; B and the cube are compact and non-empty, so the suprema are maxima
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 22, Lemma 5.5; proof pp. 22–23

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 5.5 (p. 22): Remez-type anti-concentration. One universal constant `C` (for both
`O(·)`) such that for every `d ≥ 1`, `k ≥ 1`, non-zero `p ∈ ℝ[x]_{≤k}` and `t > 0`:
(Gaussian) for every `µ`, `Σ ≻ 0`, `L > 0` and `B = {x : ‖Σ^{−1/2}(x − µ)‖₂ ≤ L}`,
`P_{X∼N(µ,Σ)}[X ∈ B and |p(X)| < t · sup_B |p|] ≤ C (d + L²) t^{1/k}`; (cube) for every
`ρ > 0`, `P_{X∼Unif([−ρ,ρ]^d)}[|p(X)| < t · sup_{[−ρ,ρ]^d} |p|] ≤ C d t^{1/k}`. -/
theorem lemma_5_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
      ∀ p : MvPolynomial (Fin d) ℝ, p ≠ 0 → p.totalDegree ≤ k →
      ∀ t : ℝ, 0 < t →
        (∀ (μ : Vec d) (Sig : Mat d), Sig.PosDef → ∀ L : ℝ, 0 < L →
          gaussian μ Sig {x | ‖mulV (invSqrt Sig) (x - μ)‖ ≤ L ∧
              |peval p x| < t * supAbs p {y | ‖mulV (invSqrt Sig) (y - μ)‖ ≤ L}} ≤
            ENNReal.ofReal (C * ((d : ℝ) + L ^ 2) * t ^ (1 / (k : ℝ)))) ∧
        (∀ ρ : ℝ, 0 < ρ →
          cubeUnif d ρ {x | |peval p x| < t * supAbs p (cube d ρ)} ≤
            ENNReal.ofReal (C * (d : ℝ) * t ^ (1 / (k : ℝ)))) := by sorry

end TruncLowDeg.Recovery
