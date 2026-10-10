-- Prove2me | Theorems.Thm_WassMMSE_FW_inner_loop_terminates
-- name    : WassMMSE.FW.inner_loop_terminates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:23.407898+00:00
-- url     : https://prove2.me/theorems/83ff1887-97ed-4639-8253-b0e27ae7768c
-- title:
--   Proof of Theorem 6.2, p. 25 — every β_t ≥ β passes (6.5), so the inner line-search loop of Algorithm 1 terminates
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points, an inexact oracle $F$ with precision $\delta\in[0,1]$), assume that $f$ is $\beta$-smooth on $\mathcal S$. Fix $s\in\mathcal S$ and write $d=F(s)-s$, $g=-d^\top\nabla f(s)$ and $\eta(b)=\min\{1,g/(b\|d\|^2)\}$. Then:
--
--   1. every trial parameter $b\ge\beta$ passes the sufficient-decrease test (6.5),
--   $$f\big(s+\eta(b)d\big)\le f(s)-\eta(b)g+\frac{\eta(b)^2b}{2}\|d\|^2;$$
--   2. consequently, for every starting value $c>0$ and every $\tau>1$ there is a smallest $j\in\{0,1,2,\dots\}$ such that $b=c\,\tau^j$ passes (6.5): the parameter $c\tau^j$ passes and $c\tau^i$ fails for every $i<j$.
--
--   With $c=\beta_{t-1}/\zeta$ this says that the inner while loop of Algorithm 1 stops after finitely many multiplications by $\tau$, so every iteration of the algorithm is well defined.
--
--   **Formalization Note** The page also gives the explicit iteration bound $\lceil\log(\zeta\beta/\beta_{-1})/\log\tau\rceil$, in which $\beta_{-1}$ should read $\beta_{t-1}$; the bound is not stated here, only termination.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, proof of Theorem 6.2, after (6.9)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- Proof of Theorem 6.2, p. 25: under Assumption 6.1 (i), at every `s ∈ 𝒮` any trial parameter
`b ≥ β` satisfies (6.5), so the inner while loop of Algorithm 1 terminates: for every start value
`c > 0` (`= β_{t−1}/ζ`) and every `τ > 1` there is a smallest `j` such that `c τ^j` satisfies (6.5). -/
theorem inner_loop_terminates
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β : ℝ} (hβ : IsSmoothOn S f β) {s : BlockSpace K d} (hs : s ∈ S) :
    (∀ b : ℝ, β ≤ b → LineSearchAccepts f F s b) ∧
      ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 1 < τ →
        ∃ j : ℕ, LineSearchAccepts f F s (c * τ ^ j) ∧
          ∀ i < j, ¬ LineSearchAccepts f F s (c * τ ^ i) := by sorry

end WassMMSE.FW
