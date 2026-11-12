-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_theorem_14
-- name    : ParallelLpSCO.EpochDA.theorem_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:22.157942+00:00
-- url     : https://prove2.me/theorems/eebe3541-9beb-4784-9eec-961d1a67611c
-- title:
--   Theorem 14 — parallel EpochDA solves heavy-tailed ℓp SCO with $O(d^{p/(2(p+1))}\kappa^{p/(p+1)}\log^4(d\kappa))$ query depth, and the printed total-query, depth and work bounds
-- statement:
--   Fix $p\in[2,\infty)$, $q=p/(p-1)$. In **Problem 1**, $f:\mathbb R^d\to\mathbb R$ is convex and is accessed only through a stochastic gradient oracle $g$ with $\mathbb E[g(x)]\in\partial f(x)$ and $\mathbb E\|g(x)\|_q^q\le L^q$ for all $x$ (heavy-tailed: only a $q$-th moment, $q\in(1,2]$). The goal is a point $\hat x$ with $\mathbb E f(\hat x)\le\min_{x\in B_p(0,R)}f(x)+\epsilon_{opt}$, with queries submitted in parallel rounds. Let $\kappa=LR/\epsilon_{opt}$.
--
--   **Theorem 14.** BallAccel (Proposition 11) using parallel EpochDA (Algorithm 9) as a ball optimization oracle solves Problem 1 with expected error $\epsilon_{opt}$, with
--   $$O\big(d^{\frac p{2(p+1)}}\kappa^{\frac p{p+1}}\log^4(d\kappa)\big)\ \text{query depth},$$
--   $$O\big(d^{\frac p{2(p+1)}}\kappa^{\frac p{p+1}}\log^4(d\kappa)+d^{\frac{p(p-2)}{2(p+1)}}\kappa^{\frac{p(2p-1)}{p+1}}\log^{2p(p-1)+2}(d\kappa)\big)\ \text{total queries},$$
--   and an additional computational cost of that same order in depth and of that order times $d$ in work.
--
--   The Lean statement: there exist one program $A$ of the parallel stochastic first-order machine (`Machine`) and one constant $C>0$, depending only on $p$, such that for every $d\ge1$, $L,R,\epsilon>0$, convex $f$ and measurable Problem 1 oracle $g$, with $\ell=\max\{1,\log(d\kappa)\}$,
--   $$D_1=d^{\frac p{2(p+1)}}\kappa^{\frac p{p+1}}\ell^4,\qquad D_2=d^{\frac{p(p-2)}{2(p+1)}}\kappa^{\frac{p(2p-1)}{p+1}}\ell^{2p(p-1)+2}:$$
--   - on **every** tape the run of $A$ on input $(d,L,R,\epsilon)$ halts with query depth $\le C(1+D_1)$, total queries $\le C(1+D_1+D_2)$, computational depth $\le C(1+D_1+D_2)$ and work $\le C(1+D_1+D_2)\,d$;
--   - for random tapes with the machine's law, $f(\hat x)$ is integrable and $\mathbb E f(\hat x)\le f(y)+\epsilon$ for every $y\in B_p(0,R)$.
--
--   For $p=2$ the query depth $\tilde O(d^{1/3}\kappa^{2/3})$ matches the Euclidean parallel rate of Carmon et al. For $L_p=R_p=1$ it improves on the $O(\epsilon_{opt}^{-p})$ query depth of stochastic ℓp mirror descent when $\epsilon_{opt}\le d^{-1/(2p)}$, up to logarithmic factors (p. 4).
--
--   **Formalization Note.** The algorithm sees only its input $(d,L,R,\epsilon)$, its random tapes and the oracle's answers. Its primitives (fixed in `Machine`) never involve $f$. Costs are counted as in `Machine`: `rounds` = query depth, `queries` = total queries, `depth` = parallel computation steps, `work` = lanes times $d$ (vector) or $1$ (scalar).
--
--   Differences from the source:
--   - encoding: a stochastic gradient oracle g with E[g(x)] ∈ ∂f(x) and E‖g(x)‖_q^q ≤ L^q (Problem 1) → a jointly measurable map g(x, u) of the query point and one uniform draw u ∈ [0, 1] (`IsGradOracle`); each query uses a fresh draw; reason: every Markov kernel into ℝ^d is the law of such a map, so the class of oracles is the same; measurability in x is the field's standing convention, needed for expectations over random query points
--   - reading: O(·) bounds (no constant, no range of κ) → C (1 + ·) with one constant C > 0 depending only on p, chosen before d, L, R, ε, f, g; reason: O(·) as an explicit constant fixed before the instance; for κ ≥ 1 the bracket is at most twice the printed quantity, while for κ < 1 (ε > LR) the printed quantities tend to 0 and no algorithm can meet them (INSIGHTS I1)
--   - reading: log(dκ) in every bound → ℓ = max{1, log(dκ)}; reason: the literal log(dκ) tends to 0 (and turns negative) as dκ decreases to 1 and below, forcing zero rounds while ε < LR (INSIGHTS I1)
--   - reading: BallAccel (Proposition 11) using parallel EpochDA (Algorithm 9) → there exists a program A of the pinned parallel stochastic first-order machine; reason: Proposition 11's BallAccel is 'an implementation' whose constants are only 'sufficiently large', so the algorithm is not pinned; the theorem's content is the existence of such an algorithm with these costs
--   - reading: query depth, total queries, depth and work (deterministic or expected not said) → bounds on every run (every tape); reason: the proof enforces deterministic caps (aborted executions, at most ⌈log₂(128κ)⌉ restarts); bounds on every run are the strongest reading
--   - encoding: the paper's informal parallel model ([CJJ+23]: oracle queries of O(1) depth, updates and vector operations of constant depth, work ×d) → the Machine model: parallel rounds of queries, parallel computation steps over a fixed f-free primitive set including the ℓp proximal map, work d per vector primitive; reason: the paper never formalizes its machine; the model counts exactly the operations the paper counts
--   - encoding: E[f(x̂)] ≤ min_{x⋆ ∈ B(R)} f(x⋆) + ε_opt → f(x̂) is integrable and E f(x̂) ≤ f(y) + ε for every y with ‖y‖_p ≤ R; reason: the minimum over the compact ball is attained, so the two are equivalent; Lean's integral of a non-integrable function is 0, so existence is stated
--   - encoding: d ≥ 1, L > 0, R > 0, ε_opt > 0; p ∈ [2, ∞) → the same, as hypotheses; p a real number ≥ 2; reason: standing assumptions of §1.3 and Problem 1
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 65, Theorem 14

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Machine

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Theorem 14 (p. 65). For every `p ≥ 2` there are one program `A` of the parallel stochastic
first-order machine and one constant `C > 0` such that, for every `d ≥ 1`, `L, R, ε > 0`, every
convex `f` on `ℝ^d` and every measurable Problem 1 oracle `g` for `f` with constant `L`, the run of
`A` on input `(d, L, R, ε)` halts on every tape with query depth, total queries, computational
depth and work bounded as printed (with `κ = LR/ε`, `ℓ = max{1, log(dκ)}`, each `O(·)` read as
`C(1 + ·)`), and the output `x̂` satisfies `E f(x̂) ≤ f(y) + ε` for every `y ∈ B_p(0, R)`. -/
theorem theorem_14 (p : ℝ) (hp : 2 ≤ p) :
    ∃ (A : Program) (C : ℝ), 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R → 0 < ε →
      ∀ (f : Vec d → ℝ), ConvexOn ℝ Set.univ f →
      ∀ (g : Oracle d), Measurable (Function.uncurry g) → IsGradOracle p L f g →
        let κ : ℝ := L * R / ε
        let ℓ : ℝ := max 1 (Real.log (d * κ))
        let D₁ : ℝ := (d : ℝ) ^ (p / (2 * (p + 1))) * κ ^ (p / (p + 1)) * ℓ ^ 4
        let D₂ : ℝ := (d : ℝ) ^ (p * (p - 2) / (2 * (p + 1))) *
          κ ^ (p * (2 * p - 1) / (p + 1)) * ℓ ^ (2 * p * (p - 1) + 2)
        (∀ tp : Tapes d, ∃ n : ℕ,
          (run p A g tp L R ε n).halted = true ∧
          ((run p A g tp L R ε n).rounds : ℝ) ≤ C * (1 + D₁) ∧
          ((run p A g tp L R ε n).queries : ℝ) ≤ C * (1 + (D₁ + D₂)) ∧
          ((run p A g tp L R ε n).depth : ℝ) ≤ C * (1 + (D₁ + D₂)) ∧
          ((run p A g tp L R ε n).work : ℝ) ≤ C * (1 + (D₁ + D₂)) * d) ∧
        (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (T : Ω → Tapes d), IsTapeLaw p P T →
          Integrable (fun ω => f (output p A g (T ω) L R ε)) P ∧
          ∀ y : Vec d, lpNorm p y ≤ R →
            ∫ ω, f (output p A g (T ω) L R ε) ∂P ≤ f y + ε) := by sorry

end ParallelLpSCO.EpochDA
