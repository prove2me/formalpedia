-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_I_9
-- name    : RollingProbeQN.Convex.Supplement.theorem_I_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:48:15.687201+00:00
-- url     : https://prove2.me/theorems/82a28696-a7e1-4887-8d8e-8786dc9dcdd3
-- title:
--   Theorem I.9 — RP-OQN model variant: $\varepsilon$-stationarity for every $\varepsilon>0$ with $62\Phi_0\sqrt{L_2}\chi^{1/3}\varepsilon^{-3/2}+13\chi^{1/3}+\chi$ gradients
-- statement:
--   Let $f$ satisfy Assumption 5.1, write $\Phi_0=f(x_0)-\inf f$, let $\varepsilon>0$ and $\nu\le\varepsilon/8$, and run the model variant of Algorithm 3 with
--   $$D=\sqrt{\frac{\varepsilon}{26L_2\chi^{2/3}}},\qquad\eta=\frac1{2\sqrt3\,\chi L_2D},\qquad T=\big\lceil(16\sqrt3\,\chi)^{1/3}\big\rceil,$$
--   $\nu$-approximate subproblem solutions, and $N=KT$ iterations. Then, for every solver with the $\nu$-approximation property:
--
--   1. two oracles that agree at every query of the first $N$ iterations (warm-up included) give the same run;
--   2. for every $K\ge1$ and every episode $k^\star$ minimizing $\|G_k\|$,
--   $$\|\nabla f(\bar w_{k^\star})\|\le\frac{\Phi_0}{DKT}+\frac34\varepsilon ;$$
--   3. in particular, if $K\ge1$ and $K\ge4\Phi_0/(DT\varepsilon)$, then $\|\nabla f(\bar w_{k^\star})\|\le\varepsilon$;
--   4. with $K=\max\{1,\lceil4\Phi_0/(DT\varepsilon)\rceil\}$, the total number of gradient queries is at most
--   $$G_\varepsilon\le62\,\Phi_0\sqrt{L_2}\,\chi^{1/3}\varepsilon^{-3/2}+13\,\chi^{1/3}+\chi .$$
--
--   Unlike Theorem 5.2, $\varepsilon$ has no upper bound here, and the stationarity clause is stated for every $K$ above the threshold.
--
--   **Formalization Note** The theorem holds for every solver whose outputs are $\nu$-approximate solutions (31) on every input with symmetric $B$ and $\|\Delta_n\|\le D$; the gradient count is the number of oracle calls, warm-up included.
--
--   Differences from the source:
--   - reading: "ν-approximate subproblem solutions" (not unique) → every solver satisfying IsNuSolver (outputs are ν-approximate on every symmetric input, step-indexed); reason: every admissible choice of Δ_{n+1} along the run is realized by such a solver (SUPPLEMENT.md decision 2)
--   - reading: "the total number of gradient queries" → the length of the run's oracle query list, with oracle locality; reason: base readings R3, R4
--   - encoding: k★ ∈ argmin_k ‖G_k‖ → the bounds for every minimizing k★; reason: ties are not broken by the paper
--   - encoding: i_n = ((n − 1) mod χ) + 1 → 0-based label (n − 1) % χ; partition with χ ≥ 1; reason: base readings R5, R7
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem I.9, p. 75 (Algorithm 3, p. 20; proof p. 75)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_OQN

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem I.9 (RP-OQN, model variant, every `ε > 0`).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem I.9, p. 75: "Let Assumption 5.1
hold, let `ε > 0`, and run the model variant of Algorithm 3 with `D = √(ε/(26 L2χ^{2/3}))`,
`η = 1/(2√3 χL2D)`, `T = ⌈(16√3 χ)^{1/3}⌉`, `ν ≤ ε/8`. Then for every `K ≥ 1`,
`‖∇f(w̄k★)‖ ≤ Φ0/(DKT) + 3/4 ε`. In particular, if `K ≥ 4Φ0/(DTε)`, the output satisfies
`‖∇f(w̄k★)‖ ≤ ε`, and with `K = max{1, ⌈4Φ0/(DTε)⌉}` the total number of gradient queries is at most
`Gε ≤ 62 Φ0 √L2 χ^{1/3}ε^{−3/2} + 13 χ^{1/3} + χ`."

Here `Φ₀ = f(x₀) − inf f` (p. 18), the run uses `N = KT` iterations, and `w̄_{k★}` is the average of the
midpoints of an episode `k★` minimizing `‖G_k‖`, `G_k` the sum of the observed gradients at the midpoints
of episode `k`.

For every instance of Assumption 5.1, every `ε > 0`, every `ν ≤ ε/8` and every solver returning
ν-approximate subproblem solutions, the run of the model variant against `G = ∇f` satisfies:
1. oracle locality: two oracles that agree at every query of the first `N` iterations (warm-up
   included) give the same state after `N` iterations;
2. for every `K ≥ 1` and every minimizing `k★`, `‖∇f(w̄_{k★})‖ ≤ Φ₀/(DKT) + 3ε/4`;
3. if `K ≥ 1` and `K ≥ 4Φ₀/(DTε)`, then `‖∇f(w̄_{k★})‖ ≤ ε` for every minimizing `k★`;
4. with `K = max{1, ⌈4Φ₀/(DTε)⌉}` the run of `KT` iterations makes at most
   `62Φ₀√L₂ χ^{1/3}ε^{−3/2} + 13χ^{1/3} + χ` oracle calls.

**Formalization Note.** The ν-approximate solutions are not unique: the statement holds for every
solver satisfying `IsNuSolver` (reading of `SUPPLEMENT.md`, decision 2). Readings R3, R4 of the base
mission: the count is the number of oracle calls, warm-up included. -/
theorem theorem_I_9 :
    ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ : ℝ) (S : Set (Fin d × Fin d))
      (grp : Fin d → Fin χ) (x₀ : EuclideanSpace ℝ (Fin d)) (ε ν : ℝ)
      (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
        Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Assumption51 d χ f L₁ L₂ S grp → 0 < ε → ν ≤ ε / 8 →
      let D : ℝ := Real.sqrt (ε / (26 * L₂ * (χ : ℝ) ^ ((2 : ℝ) / 3)))
      let η : ℝ := 1 / (2 * Real.sqrt 3 * (χ : ℝ) * L₂ * D)
      let T : ℕ := ⌈(16 * Real.sqrt 3 * (χ : ℝ)) ^ ((1 : ℝ) / 3)⌉₊
      let cfg : OQNConfig d χ := ⟨grp, S, D, η, true⟩
      let Φ₀ : ℝ := f x₀ - ⨅ x, f x
      let K₀ : ℕ := max 1 ⌈4 * Φ₀ / (D * (T : ℝ) * ε)⌉₊
      IsNuSolver D η ν solver →
      (∀ (G G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (N : ℕ),
        (∀ p ∈ oqnAllQueries cfg G solver x₀ N, G p = G' p) →
          oqnRun cfg G solver x₀ N = oqnRun cfg G' solver x₀ N) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ kstar : ℕ,
        IsBestEpisode (fun n => (oqnRun cfg (gradient f) solver x₀ n).gw) T K kstar →
        ‖gradient f (epAvg (fun n => (oqnRun cfg (gradient f) solver x₀ n).w) T kstar)‖ ≤
          Φ₀ / (D * (K : ℝ) * (T : ℝ)) + 3 / 4 * ε) ∧
      (∀ K : ℕ, 1 ≤ K → 4 * Φ₀ / (D * (T : ℝ) * ε) ≤ (K : ℝ) → ∀ kstar : ℕ,
        IsBestEpisode (fun n => (oqnRun cfg (gradient f) solver x₀ n).gw) T K kstar →
        ‖gradient f (epAvg (fun n => (oqnRun cfg (gradient f) solver x₀ n).w) T kstar)‖ ≤ ε) ∧
      ((oqnAllQueries cfg (gradient f) solver x₀ (K₀ * T)).length : ℝ) ≤
        62 * Φ₀ * Real.sqrt L₂ * (χ : ℝ) ^ ((1 : ℝ) / 3) * ε ^ (-(3 : ℝ) / 2) +
          13 * (χ : ℝ) ^ ((1 : ℝ) / 3) + (χ : ℝ) := by sorry

end RollingProbeQN.Convex.Supplement
