-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_B_3
-- name    : RollingProbeQN.Convex.Supplement.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:48:57.817282+00:00
-- url     : https://prove2.me/theorems/dc70693a-e9e4-40b3-87e8-f954101baea8
-- title:
--   Theorem B.3 — RP-OQN gradient variant: $\varepsilon$-stationarity with $72\Phi_0L_1^{1/2}L_2^{1/4}\varepsilon^{-7/4}+12(L_1^2/(L_2\varepsilon))^{1/4}$ gradients
-- statement:
--   Let $f$ satisfy Assumption 5.1, write $\Phi_0=f(x_0)-\inf f$, let $0<\varepsilon\le L_1^2/L_2$, and run the gradient variant of Algorithm 3 ($B_n=0$, no probes, $\Delta_{n+1}=\Pi_D(\Delta_n-\eta\theta_n-\eta\nabla f(z_n))$) with
--   $$D=\frac{\varepsilon^{3/4}}{9L_1^{1/2}L_2^{1/4}},\qquad\eta=\frac1{\sqrt3\,L_1},\qquad T=\Big\lceil\Big(\frac{8\sqrt3\,L_1}{L_2D}\Big)^{1/3}\Big\rceil .$$
--   Then:
--
--   1. $T\le6\,(L_1^2/(L_2\varepsilon))^{1/4}$;
--   2. two oracles that agree at every query of the first $N$ iterations give the same run;
--   3. for every $K\ge1$ and every episode $k^\star$ minimizing $\|G_k\|$, $\|\nabla f(\bar w_{k^\star})\|\le\Phi_0/(DKT)+\frac34\varepsilon$;
--   4. with $K=\max\{1,\lceil4\Phi_0/(DT\varepsilon)\rceil\}$, $\|\nabla f(\bar w_{k^\star})\|\le\varepsilon$ for every minimizing $k^\star$, after at most
--   $$G_\varepsilon\le72\,\Phi_0L_1^{1/2}L_2^{1/4}\varepsilon^{-7/4}+12\Big(\frac{L_1^2}{L_2\varepsilon}\Big)^{1/4}\tag{37}$$
--   gradient queries.
--
--   This first-order rate $O(\varepsilon^{-7/4})$ is the fallback that Theorem 5.2 selects when the rolling model does not pay.
--
--   **Formalization Note** The run takes a solver argument that the gradient variant never calls; the statement holds for every solver. The gradient count is the number of oracle calls.
--
--   Differences from the source:
--   - reading: "after at most the following number of gradient queries" → the length of the run's oracle query list, with oracle locality; reason: base readings R3, R4
--   - encoding: the gradient variant (no subproblem solver) → a run with a solver argument that is never called; the statement holds for every solver; reason: one run definition serves both variants
--   - encoding: k★ ∈ argmin_k ‖G_k‖ → the bounds for every minimizing k★; reason: ties are not broken by the paper
--   - encoding: partition g_1, …, g_χ of [d] in Assumption 5.1 → 0 < χ and a surjective 0-based group map; reason: base reading R7
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem B.3, p. 31 (Algorithm 3, p. 20; proof Appendix I.10)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_OQN

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem B.3 (RP-OQN, gradient variant).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem B.3, p. 31: "Let Assumption 5.1
hold, let `0 < ε ≤ L1²/L2`, and run the gradient variant of Algorithm 3 with
`D = ε^{3/4}/(9 L1^{1/2} L2^{1/4})`, `η = 1/(√3 L1)`, `T = ⌈(8√3 L1/(L2D))^{1/3}⌉ ≤ 6 (L1²/(L2ε))^{1/4}`.
Then for every `K ≥ 1`, `‖∇f(w̄k★)‖ ≤ Φ0/(DKT) + 3/4 ε`, and with `K = max{1, ⌈4Φ0/(DTε)⌉}` the output
satisfies `‖∇f(w̄k★)‖ ≤ ε` after at most the following number of gradient queries:
`Gε ≤ 72 Φ0 L1^{1/2} L2^{1/4} ε^{−7/4} + 12 (L1²/(L2ε))^{1/4}`. (37)"

The gradient variant has `B_n = 0`, no probes, and the explicit update
`Δ_{n+1} = Π_D(Δ_n − ηθ_n − η∇f(z_n))` (p. 20). `Φ₀ = f(x₀) − inf f`.

For every instance of Assumption 5.1 and every `0 < ε ≤ L₁²/L₂`, with the stated parameters:
1. `T ≤ 6(L₁²/(L₂ε))^{1/4}`;
2. oracle locality of the run, as in Theorem I.9;
3. for every `K ≥ 1` and every minimizing `k★`, `‖∇f(w̄_{k★})‖ ≤ Φ₀/(DKT) + 3ε/4`;
4. with `K = max{1, ⌈4Φ₀/(DTε)⌉}`, `‖∇f(w̄_{k★})‖ ≤ ε` for every minimizing `k★`, and the run of `KT`
   iterations makes at most `72Φ₀L₁^{1/2}L₂^{1/4}ε^{−7/4} + 12(L₁²/(L₂ε))^{1/4}` oracle calls.

**Formalization Note.** The run takes a solver argument, which the gradient variant never calls; the
statement holds for every solver. Readings R3, R4 of the base mission: the count is the number of
oracle calls. -/
theorem theorem_B_3 :
    ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ : ℝ) (S : Set (Fin d × Fin d))
      (grp : Fin d → Fin χ) (x₀ : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
      (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
        Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Assumption51 d χ f L₁ L₂ S grp → 0 < ε → ε ≤ L₁ ^ 2 / L₂ →
      let D : ℝ := ε ^ ((3 : ℝ) / 4) / (9 * L₁ ^ ((1 : ℝ) / 2) * L₂ ^ ((1 : ℝ) / 4))
      let η : ℝ := 1 / (Real.sqrt 3 * L₁)
      let T : ℕ := ⌈(8 * Real.sqrt 3 * L₁ / (L₂ * D)) ^ ((1 : ℝ) / 3)⌉₊
      let cfg : OQNConfig d χ := ⟨grp, S, D, η, false⟩
      let Φ₀ : ℝ := f x₀ - ⨅ x, f x
      let K₀ : ℕ := max 1 ⌈4 * Φ₀ / (D * (T : ℝ) * ε)⌉₊
      (T : ℝ) ≤ 6 * (L₁ ^ 2 / (L₂ * ε)) ^ ((1 : ℝ) / 4) ∧
      (∀ (G G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (N : ℕ),
        (∀ p ∈ oqnAllQueries cfg G solver x₀ N, G p = G' p) →
          oqnRun cfg G solver x₀ N = oqnRun cfg G' solver x₀ N) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ kstar : ℕ,
        IsBestEpisode (fun n => (oqnRun cfg (gradient f) solver x₀ n).gw) T K kstar →
        ‖gradient f (epAvg (fun n => (oqnRun cfg (gradient f) solver x₀ n).w) T kstar)‖ ≤
          Φ₀ / (D * (K : ℝ) * (T : ℝ)) + 3 / 4 * ε) ∧
      (∀ kstar : ℕ,
        IsBestEpisode (fun n => (oqnRun cfg (gradient f) solver x₀ n).gw) T K₀ kstar →
        ‖gradient f (epAvg (fun n => (oqnRun cfg (gradient f) solver x₀ n).w) T kstar)‖ ≤ ε) ∧
      ((oqnAllQueries cfg (gradient f) solver x₀ (K₀ * T)).length : ℝ) ≤
        72 * Φ₀ * L₁ ^ ((1 : ℝ) / 2) * L₂ ^ ((1 : ℝ) / 4) * ε ^ (-(7 : ℝ) / 4) +
          12 * (L₁ ^ 2 / (L₂ * ε)) ^ ((1 : ℝ) / 4) := by sorry

end RollingProbeQN.Convex.Supplement
