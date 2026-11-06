-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_theorem_3_1
-- name    : RollingProbeQN.Convex.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:30:44.02096+00:00
-- url     : https://prove2.me/theorems/78b3944e-3c53-4cea-927f-958e1e0e13d7
-- title:
--   Theorem 3.1 — RP-QNPE uses three gradients per iteration and attains $f(x_k)-f^\star\le O_\sigma(\min\{L_1R^2/k^2,\chi(L_1+L_2R)R^2/k^3\})$
-- statement:
--   **Theorem 3.1.** Fix $\sigma\in(0,1)$. There is a constant $C>0$ depending only on $\sigma$ such that the following holds for every dimension $d$, number of groups $\chi$, function $f$, constants $L_1,L_2,R$, pattern $\mathcal S$, structurally orthogonal partition, start $x_0$ and minimizer $x^\star$ satisfying Assumption 2.1. Run Algorithm 1 (RP-QNPE) with Subroutine 1.1 and $b=L_2R$.
--
--   1. **Three gradients per iteration.** For every gradient oracle $G$, each iteration queries $G$ at most three times, and two oracles that agree at all points queried before iteration $k$ produce the same state at iteration $k$.
--   2. **Rate (11).** With exact gradients, for every $k\ge1$,
--   $$f(x_k)-f^\star\ \le\ C\min\Big\{\frac{L_1R^2}{k^2},\ \frac{\chi(L_1+L_2R)R^2}{k^3}\Big\}.$$
--   3. **Gradient complexity (12).** For every $\varepsilon>0$, the method with target $\varepsilon$ returns a point $\hat x$ with $f(\hat x)-f^\star\le\varepsilon$ after $G_\varepsilon$ gradient queries, where
--   $$G_\varepsilon\ \le\ C\Big(1+\min\Big\{\sqrt{\frac{L_1R^2}{\varepsilon}},\ \Big(\frac{\chi(L_1+L_2R)R^2}{\varepsilon}\Big)^{1/3}\Big\}\Big).$$
--
--   For fixed $L_1,L_2,R,\sigma$ the bounds read $O(\min\{k^{-2},\chi k^{-3}\})$ and $O(1+\min\{\varepsilon^{-1/2},\chi^{1/3}\varepsilon^{-1/3}\})$, with no logarithmic factor and no additive $\chi$. The effective dimension $\chi\le d$ comes from a structurally orthogonal partition of the Hessian's sparsity pattern; $\chi=d$ in the dense case.
--
--   **Formalization Note** The algorithm is defined against an abstract oracle $G$ and the rate and complexity are stated with $G=\nabla f$. $C$ is chosen after $\sigma$ and before all other data.
--
--   Differences from the source:
--   - reading: O_σ(·) → ∃ C > 0 chosen after σ and before d, χ, f, L₁, L₂, R, S, the partition, x₀, x★, k and ε; reason: p. 7 ("All O_σ(·) constants may depend on a fixed σ") and p. 52 ("All displayed constants depend only on σ") (reading R1)
--   - reading: uses at most three gradients per iteration → for every oracle G each iteration's query list has length ≤ 3, and oracles agreeing on the queries made so far give the same run; reason: a length bound alone would say nothing; this is the oracle-model meaning of the count (reading R3)
--   - encoding: (11) for the method; (12) for the method with target ε → (11) for the run without Step 5, frozen after a return at ∇f(x_k) = 0; (12) for the run stopped at its first return (epsReturns, epsOutput); reason: Step 5 only stops the run, and a frozen x_k is a minimizer (reading R2)
--   - encoding: G_ε gradient queries → the length of allQueries (k + 1) at the first return k, including ∇f(x₀); reason: initialization computes ∇f(x₀) (p. 52) (reading R4)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem 3.1, p. 11

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_allQueries
import Definitions.Def_RollingProbeQN_Convex_epsReturns
import Definitions.Def_RollingProbeQN_Convex_epsOutput

namespace RollingProbeQN.Convex

/-- **Theorem 3.1 (RP-QNPE: three gradients per iteration, rate and gradient complexity).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem 3.1, p. 11: "Under Assumption 2.1, Algorithm 1 with Subroutine 1.1 and `b = L2R` uses at
most three gradients per iteration, and for all `k ≥ 1`
`f(x_k) − f★ ≤ O_σ(min{L1R²/k², χ(L1 + L2R)R²/k³})`. (11) Consequently, for any `ε > 0`, it returns
an `ε`-accurate point after `G_ε` gradient queries, where
`G_ε = O_σ(1 + min{√(L1R²/ε), (χ(L1 + L2R)R²/ε)^{1/3}})`. (12)"

For every `σ ∈ (0, 1)` there is `C > 0` such that, for every dimension `d`, number of groups `χ`,
function `f`, constants `L₁, L₂, R`, pattern `S`, structurally orthogonal partition `grp`, start `x₀`
and minimizer `x★` satisfying Assumption 2.1, the run of Algorithm 1 with `b = L₂R`:
1. calls the oracle at most three times per iteration, at the listed points only: for every oracle
   `G`, each iteration's query list has length at most 3, and two oracles that agree at every query made
   before iteration `k` produce the same state at iteration `k`;
2. with `G = ∇f`, satisfies (11) with constant `C` for every `k ≥ 1`;
3. with `G = ∇f` and target `ε > 0`, returns at some iteration `k` (its first return), with an
   `ε`-accurate output, after at most `C(1 + min{√(L₁R²/ε), (χ(L₁ + L₂R)R²/ε)^{1/3}})` oracle calls.

**Formalization Note.** Reading R1: `O_σ` is a constant `C` chosen after `σ` and before all the data,
as p. 52 says ("All displayed constants depend only on `σ`"). Reading R2: the run without the stopping
rule of Step 5 is frozen after a return at a zero gradient, where `x_k` is a minimizer; (11) is about
this run, (12) about the ε-run (`epsReturns`, `epsOutput`). Reading R3: "uses at most three gradients
per iteration" is the oracle model of clause 1; the run is a function of the oracle `G`. Reading R4:
the count includes the initial query `∇f(x₀)`. -/
theorem theorem_3_1 :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ R : ℝ) (S : Set (Fin d × Fin d))
        (grp : Fin d → Fin χ) (x₀ xstar : EuclideanSpace ℝ (Fin d)),
        Assumption21 d χ f L₁ L₂ R S grp x₀ xstar →
        let cfg : Config d χ := ⟨grp, S, L₁, L₂, L₂ * R, σ⟩
        (∀ (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ),
          (iterQueries cfg G x₀ k).length ≤ 3) ∧
        (∀ (G G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ),
          (∀ q ∈ allQueries cfg G x₀ k, G q = G' q) → run cfg G x₀ k = run cfg G' x₀ k) ∧
        (∀ k : ℕ, 1 ≤ k →
          f (run cfg (gradient f) x₀ k).x - f xstar ≤
            C * min (L₁ * R ^ 2 / (k : ℝ) ^ 2) (χ * (L₁ + L₂ * R) * R ^ 2 / (k : ℝ) ^ 3)) ∧
        (∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
          epsReturns cfg (gradient f) x₀ R ε k ∧
          (∀ j < k, ¬ epsReturns cfg (gradient f) x₀ R ε j) ∧
          f (epsOutput cfg (gradient f) x₀ k) - f xstar ≤ ε ∧
          ((allQueries cfg (gradient f) x₀ (k + 1)).length : ℝ) ≤
            C * (1 + min (Real.sqrt (L₁ * R ^ 2 / ε))
              ((χ * (L₁ + L₂ * R) * R ^ 2 / ε) ^ ((1 : ℝ) / 3)))) := by sorry

end RollingProbeQN.Convex
