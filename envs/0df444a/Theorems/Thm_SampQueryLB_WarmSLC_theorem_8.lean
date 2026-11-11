-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_theorem_8
-- name    : SampQueryLB.WarmSLC.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:15:19.444747+00:00
-- url     : https://prove2.me/theorems/c94990d0-d0aa-4dc1-8f8f-5d056b3cbd2b
-- title:
--   Theorem 8 — warm-start sampling of 2-conditioned strongly log-concave targets needs $\Omega(\exp(c(\log d)^{1/3}))$ queries in worst-case expectation
-- statement:
--   A potential $V\in C^\infty(\mathbb R^d)$ with $I_d\preceq\nabla^2V\preceq2I_d$ has the strongly log-concave target $\pi_V(dx)\propto e^{-V(x)}dx$ (condition number $2$). A warm-start sampling algorithm (§2.2) receives one sample $X_{\mathrm{init}}\sim\nu$ and an independent seed $\omega\sim\mathrm{Unif}[0,1]$, makes adaptive exact first-order queries $(V(y),\nabla V(y))$, stops by a Borel rule after $N$ queries and outputs $X$; $\rho^{\mathrm{Alg}}_{V,\nu}$ is the law of $X$ and $\mathbb E_{V,\nu}[N]$ the expected number of queries.
--
--   **Theorem 8.** There exist universal constants $c>0$ (and $C>0$, behind $\Omega$) and $d_0$ such that for every $d\ge d_0$ there is a family $\mathcal W_d$ of pairs $(V,\nu)$ with $V\in C^\infty(\mathbb R^d)$ and
--   1. $I_d\preceq\nabla^2V(x)\preceq2I_d$ for every $(V,\nu)\in\mathcal W_d$ and every $x$;
--   2. $V(-x)=V(x)$, the unique minimizer of $V$ is $0$, and $\pi_V$ has mean zero;
--   3. $\nu$ has a smooth, everywhere positive, even density, has mean zero, and $\frac{d\nu}{d\pi_V}\le3$, $\frac{d\pi_V}{d\nu}\le100$;
--   4. every algorithm that samples from $\{\pi_V:(V,\nu)\in\mathcal W_d\}$ with accuracy $1/10$ in total variation, uniformly over $\mathcal W_d$, when given one sample $X_{\mathrm{init}}\sim\nu$, has
--   $$\sup_{(V,\nu)\in\mathcal W_d}\mathbb E_{V,\nu}[N]\ \ge\ C\exp\big(c(\log d)^{1/3}\big).$$
--   The common minimizer and target mean may be given to the algorithm.
--
--   Even a constant-warm start does not make well-conditioned sampling dimension-free in query complexity; the bound complements the $d^{o(1)}$ upper bound for this class.
--
--   **Formalization Note.** The supremum is taken in $[0,\infty]$, so an empty family cannot satisfy item 4. Every algorithm considered must have $N<\infty$ almost surely and output law within total variation $1/10$ of $\pi_V$ on every member of $\mathcal W_d$. Since every member has minimizer $0$ and mean $0$, an algorithm "given" them is just an algorithm whose maps use these values; no extra input is encoded. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: the §2.2 algorithm: seed ω ∼ Unif[0,1], Borel query maps, stopping sets and output maps, all randomness in ω; in the warm-start model also the initial sample → WarmAlgorithm: measurable maps of ((x_init, ω), history); ω ∈ ℝ with law Unif[0,1] (seedLaw), independent of x_init; reason: the paper's model; maps on all of ℝ restrict to [0,1]
--   - encoding: TV(·,·) = sup over measurable B of |ν(B) − ν'(B)| → TVAtMost μ ν ε (LogConcaveQuery): |μ.real B − ν.real B| ≤ ε for every measurable B; laws as Measure.map; reason: the same quantity, TV ≤ ε iff every measurable set is within ε
--   - encoding: Ω(exp(c (log d)^{1/3})) queries in worst-case expectation → ∃ C > 0 (placed with c, before d0) with ofReal (C exp(c (log d)^{1/3})) ≤ ⨆_{(V,ν) ∈ W_d} E_{V,ν}[N] in ℝ≥0∞; reason: the definition of Ω with a universal constant; the supremum of expected query counts is the worst-case expectation
--   - encoding: V ∈ C^∞; I_d ⪯ ∇²V ⪯ 2I_d; unique minimizer 0; mean zero; ν with a smooth positive even density, dν/dπ_V ≤ 3, dπ_V/dν ≤ 100 → ContDiff ℝ ∞; HessianBetween V 1 2 (quadratic form of the derivative of the gradient); ∀ x ≠ 0, V 0 < V x; MeanZero; IsProbabilityMeasure ν ∧ HasSmoothPosEvenDensity ν ∧ MeanZero ν ∧ RatioBounds ν π_V 3 100; reason: the paper's definitions; C^∞ is ∞ = (⊤ : ℕ∞), not the analytic class ω
--   - encoding: algorithms with N < ∞ almost surely on every potential considered; 'the common minimizer and target mean may be given to the algorithm' → FiniteQueriesAS as part of the hypothesis on each member; no extra input; reason: §2.2 requires N < ∞ a.s.; the minimizer and mean are 0 for every member, so a fixed algorithm can use them without being given them
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 55, Theorem 8 (PDF p. 58); proof §7.1, pp. 56–59

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model

open MeasureTheory OAI.LogConcaveSampling
open scoped ENNReal ContDiff

namespace SampQueryLB.WarmSLC

theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
      ∃ W : Set ((Point d → ℝ) × Measure (Point d)),
        (∀ p ∈ W, ContDiff ℝ ∞ p.1 ∧ HessianBetween p.1 1 2) ∧
        (∀ p ∈ W, (∀ x, p.1 (-x) = p.1 x) ∧ (∀ x, x ≠ 0 → p.1 0 < p.1 x) ∧
          MeanZero (gibbs p.1)) ∧
        (∀ p ∈ W, IsProbabilityMeasure p.2 ∧ HasSmoothPosEvenDensity p.2 ∧ MeanZero p.2 ∧
          RatioBounds p.2 (gibbs p.1) 3 100) ∧
        ∀ A : WarmAlgorithm d,
          (∀ p ∈ W, FiniteQueriesAS A p.1 p.2 ∧ TVAtMost (outputLaw A p.1 p.2) (gibbs p.1) (1 / 10)) →
          ENNReal.ofReal (C * Real.exp (c * Real.log d ^ ((1 : ℝ) / 3))) ≤
            ⨆ p ∈ W, expectedQueries A p.1 p.2 := by sorry

end SampQueryLB.WarmSLC
