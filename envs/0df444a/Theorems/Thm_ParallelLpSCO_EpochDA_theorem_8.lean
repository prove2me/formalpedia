-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_theorem_8
-- name    : ParallelLpSCO.EpochDA.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:06:32.285733+00:00
-- url     : https://prove2.me/theorems/b643e566-bb91-46b0-8796-fe80a9257cf4
-- title:
--   Theorem 8 — NextLambda returns $\lambda\in[\lambda_{\min},\lambda_{\max}]$ with $\hat\Delta(\lambda)\le r$, $\lambda<2\lambda_{\min}$ or $\hat\Delta(\lambda)\ge3r/4$, in $O(\log)$ BROO calls
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be convex and $G$-Lipschitz for $\|\cdot\|_p$. Let $x,v\in\mathbb R^d$ with $\|x-v\|_p\le2R$, $0<r\le R$, and
--   $$\hat x_\lambda=\operatorname*{argmin}_x\Big\{f(x)+\frac\lambda p\|x-y_\lambda\|_p^p\Big\},\qquad\hat\Delta(\lambda)=\|\hat x_\lambda-y_\lambda\|_p.$$
--   Given $\lambda_{\max}\ge2^{p-1}G/r^{p-1}$ and $\lambda_{\min}\in(0,\lambda_{\max})$, Algorithm 7 (NextLambda) returns $\lambda\in[\lambda_{\min},\lambda_{\max}]$ with $\hat\Delta(\lambda)\le r$. Moreover, either $\lambda<2\lambda_{\min}$, or $\lambda\in[2\lambda_{\min},\lambda_{\max}]$ and $\hat\Delta(\lambda)\in[3r/4,r)$. The overall BROO complexity is
--   $$O\Big(\log\frac{\lambda_{\max}}{\lambda_{\min}}+\log\Big(1+\frac{R+\frac1{p-1}(G/\lambda_{\min})^{1/(p-1)}}r\Big)\Big).$$
--
--   This is the line search of accelerated proximal point methods in ℓp. It guarantees each step moves a constant fraction of $r$ unless $\lambda$ is already near its floor, which is what bounds the number of ball-acceleration iterations.
--
--   **Formalization Note.** $y_\lambda$ is Algorithm 7's (`yLam`, with the input $A\ge0$); the BROO is any mapping with Definition 5's guarantee for $f$ on $\mathbb R^d$ with radius $r$. The BROO complexity is `nextLambdaCalls`, bounded by $C$ times the displayed quantity with $C$ fixed before the instance.
--
--   Differences from the source:
--   - reading: 'Algorithm ??' → Algorithm 7 (NextLambda); reason: obvious typo: §3.5.1 is about NextLambda and the proof traces its loops (INSIGHTS I3)
--   - reading: x̂_λ = argmin_x {f(x) + (λ/p)‖x − y_λ‖_p^p} → every minimizer x̂ of that objective; reason: the objective is strictly convex and coercive, so the minimizer exists and is unique
--   - encoding: the inputs x, v, A ≥ 0, λ_min, λ_max, G, R, r and a BROO of Algorithm 7 (line 1, line 3) → A ≥ 0 and any O with IsBROO p f ℝ^d r O as hypotheses; reason: Algorithm 7 takes them as input; Theorem 8 is about every admissible input
--   - reading: the overall BROO complexity is O(…) → nextLambdaCalls (one call per evaluation of ∆ in the pseudocode) ≤ C · (…) with C > 0 fixed before the instance; reason: O(·) as an explicit constant; the paper's proof counts BROO calls as evaluations of ∆
--   - encoding: f is G-Lipschitz → 0 ≤ G and |f x − f y| ≤ G‖x − y‖_p; reason: a Lipschitz constant is nonnegative; the bound's (G/λ_min)^{1/(p−1)} is undefined for G < 0
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 37, Theorem 8

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Machine
import Definitions.Def_ParallelLpSCO_EpochDA_NextLambda

namespace ParallelLpSCO.EpochDA

/-- Theorem 8 (p. 37), with "Algorithm ??" read as Algorithm 7 (NextLambda). There is `C > 0`
such that, for `f` convex and `G`-Lipschitz for `‖·‖_p`, `x, v` with `‖x − v‖_p ≤ 2R`, `A ≥ 0`,
`0 < r ≤ R`, `λ_max ≥ 2^{p−1} G / r^{p−1}`, `λ_min ∈ (0, λ_max)` and any BROO of radius `r` for
`f`, NextLambda returns `λ ∈ [λ_min, λ_max]` with `∆̂(λ) ≤ r` (`∆̂(λ) = ‖x̂_λ − y_λ‖_p`, `x̂_λ` the
unconstrained prox point), and either `λ < 2λ_min` or `λ ∈ [2λ_min, λ_max]` and
`∆̂(λ) ∈ [3r/4, r)`, using at most
`C (log(λ_max/λ_min) + log(1 + (R + (1/(p−1))(G/λ_min)^{1/(p−1)})/r))` BROO calls. -/
theorem theorem_8 (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (f : Vec d → ℝ), ConvexOn ℝ Set.univ f →
      ∀ G : ℝ, 0 ≤ G → (∀ x y, |f x - f y| ≤ G * lpNorm p (x - y)) →
      ∀ (x v : Vec d) (A R r : ℝ), 0 ≤ A → lpNorm p (x - v) ≤ 2 * R → 0 < r → r ≤ R →
      ∀ lamMin lamMax : ℝ, (2 : ℝ) ^ (p - 1) * G / r ^ (p - 1) ≤ lamMax →
        0 < lamMin → lamMin < lamMax →
      ∀ O : ℝ → ℝ → Vec d → Vec d, IsBROO p f Set.univ r O →
        let lam := nextLambda p r A G R lamMin lamMax x v O
        let y := yLam p A lam x v
        (lamMin ≤ lam ∧ lam ≤ lamMax) ∧
        (∀ xhat : Vec d, (∀ z, f xhat + lam / p * lpNorm p (xhat - y) ^ p ≤
            f z + lam / p * lpNorm p (z - y) ^ p) →
          lpNorm p (xhat - y) ≤ r ∧
          (lam < 2 * lamMin ∨
            ((2 * lamMin ≤ lam ∧ lam ≤ lamMax) ∧
              3 * r / 4 ≤ lpNorm p (xhat - y) ∧ lpNorm p (xhat - y) < r))) ∧
        (nextLambdaCalls p r A G R lamMin lamMax x v O : ℝ) ≤
          C * (Real.log (lamMax / lamMin) +
            Real.log (1 + (R + 1 / (p - 1) * (G / lamMin) ^ (1 / (p - 1))) / r)) := by sorry

end ParallelLpSCO.EpochDA
