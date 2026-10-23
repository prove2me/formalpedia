-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_proposition_1
-- name    : ProjectOutsourcing.SingleTask.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:09.557261+00:00
-- url     : https://prove2.me/theorems/7f4d5a02-cf0e-4492-b782-7b70b01c1b30
-- title:
--   Proposition 1, p. 11 — the bargaining powers at which each contract form coordinates a single-task project, and the negotiated terms (TB set read through δ^TB_S(β) = θΠ*)
-- statement:
--   Consider the single-task project of Section 3 under its standing assumptions (reward $Q>0$; duration $Z/r$ with $\mathbb E[Z]=1$ and strictly concave cdf, Assumption 1; expected cost $c$ differentiable, increasing and strictly convex with $c(0)=c'(0)=0$, Assumption 2). Let $r^*$ be the system-optimal work rate, $\Pi^*=\Pi(r^*)$, and for each contract form $m$ let $\Phi^m$ be the set of bargaining powers $\theta\in[0,1]$ at which the Nash bargaining solution of Problem B (3) coordinates the system: a solution exists, and every solution induces $r^*$. Then
--
--   1. $\Phi^{FP}=\Phi^{TF+}=\{1\}$, and at $\theta=1$ every solution has $\hat p^{FP}=Q$, respectively $\hat p^{TF+}=Q$, $\hat\beta^{TF+}=0$;
--   2. $\Phi^{TB}=\{\theta\in[0,1]:\delta^{TB}_S(\beta)=\theta\Pi^*\text{ for some }\beta\ge0\}$, which equals $[\underline\delta^{TB}_S/\Pi^*,1]$ when the minimum $\underline\delta^{TB}_S=\min_{\beta\ge0}\delta^{TB}_S(\beta)$ is attained; for $\theta\in\Phi^{TB}$ every solution has $\delta^{TB}_S(\hat\beta^{TB})=\theta\Pi^*$, $\hat\beta^{TB}\ge 0$, and
--   $$\hat p^{TB}=\frac{\alpha\,\mathbb E_Z[Ze^{-\alpha Z/r^*}]}{(\alpha+\hat\beta^{TB})\,\mathbb E_Z\big[Ze^{-(\alpha+\hat\beta^{TB})Z/r^*}\big]}\,Q ;$$
--   3. $\Phi^{TF}=\Phi^{CS}=[0,1]$, and for every $\theta\in[0,1]$ every solution has $\hat p^{TF}=Q$, $\hat\beta^{TF}=-(1-\theta)\Pi^*$, respectively $\hat p^{CS}=\theta Q$, $\hat\beta^{CS}=1-\theta$;
--   4. $\Phi^{C+}=\{0\}$, and at $\theta=0$ every solution has $\hat p^{C+}=0$, $\hat\beta^{C+}=1$;
--   5. for $m\in\{FP,TF{+},TB\}$ and $\theta\in[0,1]\setminus\Phi^m$, no solution of Problem B induces $r^*$.
--
--   This is the paper's first main result: it shows that the fixed-price and cost-plus contracts, the most common in practice, coordinate the project only under extreme bargaining power, whereas the two-part fixed-price and cost-sharing contracts coordinate it for every bargaining power.
--
--   **Formalization Note** The page prints $\Phi^{TB}=[\underline\delta^{TB}_S/\Pi^*,1]$ with $\underline\delta^{TB}_S=\min_{\beta\ge0}\delta^{TB}_S(\beta)$. In the paper's Example 1 the minimum is not attained: $\delta^{TB}_S$ is strictly decreasing and only approaches its infimum. There the printed closed interval would include an endpoint at which no term coordinates. The set is therefore stated as $\{\theta\in[0,1]:\theta\Pi^*\in\delta^{TB}_S([0,\infty))\}$, which matches the page's own definition of $\hat\beta^{TB}$ as a root of $\delta^{TB}_S(\beta)=\theta\Pi^*$ and the p. 12 phrase "above the threshold". The printed interval is also stated, under the hypothesis that the minimum is attained. Uniqueness of the root $\hat\beta^{TB}$ is not claimed. "Coordinates" means that a solution exists and every solution induces the system-optimal rate. Item 5 is not stated for C+: for $\theta>0$ every feasible C+ outcome gives the subcontractor zero profit, so a coordinating outcome is also a (non-unique) solution, and the negative side of C+ is exactly $\Phi^{C+}=\{0\}$. Footnote 1's tie-break (an indifferent subcontractor chooses the system-optimal rate) is part of the model. The added hypotheses $\alpha>0$ and integrability of the realized cost are part of the model's validity predicate.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1; (4), p. 11; restatement and footnote 1, p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem proposition_1 (M : Model) (hM : M.Valid) (rStar : ℝ) (hr : IsSystemOpt M rStar) :
    -- FP and TF+
    Phi M .FP = {1} ∧ Phi M .TFplus = {1} ∧
      (∀ x, IsNashSol M .FP 1 x → x.1.1 = M.Q) ∧
      (∀ x, IsNashSol M .TFplus 1 x → x.1 = (M.Q, 0)) ∧
      -- TB: the set of θ with θΠ* a value of δ^TB_S on [0, ∞), equal to the printed interval
      -- [δ̲^TB_S/Π*, 1] when the minimum in (4) is attained
      Phi M .TB =
        {θ | θ ∈ Set.Icc 0 1 ∧ ∃ β, 0 ≤ β ∧ deltaTB M rStar β = θ * sysProfit M rStar} ∧
      (∀ β₀, 0 ≤ β₀ → IsMinOn (deltaTB M rStar) (Set.Ici 0) β₀ →
        Phi M .TB = Set.Icc (deltaTB M rStar β₀ / sysProfit M rStar) 1) ∧
      (∀ θ ∈ Phi M .TB, ∀ x, IsNashSol M .TB θ x →
        0 ≤ x.1.2 ∧ deltaTB M rStar x.1.2 = θ * sysProfit M rStar ∧
          x.1.1 = M.alpha * discZ M M.alpha rStar /
            ((M.alpha + x.1.2) * discZ M (M.alpha + x.1.2) rStar) * M.Q) ∧
      -- TF and CS
      Phi M .TF = Set.Icc 0 1 ∧ Phi M .CS = Set.Icc 0 1 ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .TF θ x →
        x.1 = (M.Q, -(1 - θ) * sysProfit M rStar)) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .CS θ x → x.1 = (θ * M.Q, 1 - θ)) ∧
      -- C+
      Phi M .Cplus = {0} ∧ (∀ x, IsNashSol M .Cplus 0 x → x.1 = (0, 1)) ∧
      -- outside Φ^m no bargaining solution coordinates (FP, TF+, TB)
      (∀ m ∈ ({.FP, .TFplus, .TB} : Set Form), ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ Phi M m →
        ∀ x, IsNashSol M m θ x → ¬ IsSystemOpt M x.2) := by sorry

end ProjectOutsourcing.SingleTask
