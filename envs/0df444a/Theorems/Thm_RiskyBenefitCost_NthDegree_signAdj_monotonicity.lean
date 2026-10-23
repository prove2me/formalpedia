-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_signAdj_monotonicity
-- name    : RiskyBenefitCost.NthDegree.signAdj_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:16.31266+00:00
-- url     : https://prove2.me/theorems/805179cf-9991-435a-81ff-e96cd2bb000e
-- title:
--   §4, p. 3628 (PDF 5) — monotonicity of (5) in b in each of the four problem classes, by the parity of N for a risky cost
-- statement:
--   Work in the linear-payoff model with $N\ge1$, $0\le\underline x<\bar x$, $z_0\ge0$, $B\subset\mathbb R$ compact, $f$ continuous on $B$, and $U$ increasing and $(N+1)$ times continuously differentiable. Let $D\subset\mathbb R$ be an interval (an order-connected set) containing every payoff $f(b)(X-x_0)+z_0$ with $b\in B$, $X\in[\underline x,\bar x]$, and suppose that on $D$ the decision maker is strictly $N$th-degree risk averse, $(N+1)$th-degree risk averse, and has relative $(N+1)$th-degree risk aversion $r_{N+1}<N$.
--
--   Then for every $X\in[\underline x,\bar x]$, the function $b\mapsto(-1)^Nf(b)^NU^{(N)}\big(f(b)(X-x_0)+z_0\big)$ of display (5) is
--   1. decreasing on $B$ in the risk-taking problem with a risky benefit;
--   2. increasing on $B$ in the risk-mitigation problem with a risky benefit;
--   3. in the risk-taking problem with a risky cost: decreasing if $N$ is even and increasing if $N$ is odd;
--   4. in the risk-mitigation problem with a risky cost: increasing if $N$ is even and decreasing if $N$ is odd.
--
--   Combined with Lemma 3 this yields Proposition 2. The parity enters through the sign of $f(b)^{N-1}$ when $f\le0$.
--
--   **Formalization Note.** "Increasing"/"decreasing" are weak (`MonotoneOn`/`AntitoneOn`). The "relevant domain" of the utility function is the order-connected set $D$; $U$ is defined and smooth on all of $\mathbb R$ and the risk attitudes are imposed only on $D$ (a $C^{N+1}$ utility on a neighbourhood of the compact payoff range extends to $\mathbb R$). Strict $N$th-degree risk aversion is forced by Definition 4, which defines $r_{N+1}$ only where $(-1)^{N+1}U^{(N)}>0$. The hypothesis $z_0\ge0$ is added (see display (8)). $f$ is not assumed differentiable.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3628 (PDF 5), §4, paragraph after display (8)

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree

theorem signAdj_monotonicity (N : ℕ) (hN : 1 ≤ N) (xl xu x0 z0 : ℝ) (hxl : 0 ≤ xl)
    (hlt : xl < xu) (hz0 : 0 ≤ z0)
    (B : Set ℝ) (hB : IsCompact B) (f : ℝ → ℝ) (hf : ContinuousOn f B)
    (U : ℝ → ℝ) (hU : ContDiff ℝ (N + 1) U) (hUmono : Monotone U)
    (D : Set ℝ) (hD : D.OrdConnected)
    (hpay : ∀ b ∈ B, ∀ X ∈ Set.Icc xl xu, f b * (X - x0) + z0 ∈ D)
    (hRA_N : ∀ z ∈ D, 0 < (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U z)
    (hRA_N1 : NthDegreeRiskAverseOn (N + 1) U D)
    (hrel : ∀ z ∈ D, relRiskAversion N U z < N) :
    ∀ X ∈ Set.Icc xl xu,
      (RiskTakingBenefit f B → AntitoneOn (fun b => signAdj N U f x0 z0 X b) B) ∧
      (RiskMitigationBenefit f B → MonotoneOn (fun b => signAdj N U f x0 z0 X b) B) ∧
      (RiskTakingCost f B →
        (Even N → AntitoneOn (fun b => signAdj N U f x0 z0 X b) B) ∧
        (Odd N → MonotoneOn (fun b => signAdj N U f x0 z0 X b) B)) ∧
      (RiskMitigationCost f B →
        (Even N → MonotoneOn (fun b => signAdj N U f x0 z0 X b) B) ∧
        (Odd N → AntitoneOn (fun b => signAdj N U f x0 z0 X b) B)) := by sorry

end RiskyBenefitCost.NthDegree
