-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_5_2
-- name    : RollingProbeQN.Convex.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:49:34.916874+00:00
-- url     : https://prove2.me/theorems/f3c3d311-3aba-4001-98e9-3b9f1b692b2c
-- title:
--   Theorem 5.2 — RP-OQN: $\varepsilon$-stationarity with the count (34), and $G_\varepsilon=O(\min\{\chi^{1/3}\varepsilon^{-3/2},\varepsilon^{-7/4}\})$
-- statement:
--   Let $f$ satisfy Assumption 5.1, write $\Phi_0=f(x_0)-\inf f$ and let $0<\varepsilon\le L_1^2/L_2$.
--
--   1. Run the model variant of Algorithm 3 with
--   $$D=\sqrt{\frac{\varepsilon}{26L_2\chi^{2/3}}},\qquad\eta=\frac1{2\sqrt3\,\chi L_2D},\qquad T=\big\lceil(16\sqrt3\,\chi)^{1/3}\big\rceil,\qquad\nu\le\frac\varepsilon8 .$$
--   For every solver with the $\nu$-approximation property the run has oracle locality; for every $K\ge1$ and every episode $k^\star$ minimizing $\|G_k\|$, $\|\nabla f(\bar w_{k^\star})\|\le\Phi_0/(DKT)+\frac34\varepsilon$; and with $K=\max\{1,\lceil4\Phi_0/(DT\varepsilon)\rceil\}$ the output is $\varepsilon$-stationary after at most
--   $$G_\varepsilon\le62\,\Phi_0\sqrt{L_2}\,\chi^{1/3}\varepsilon^{-3/2}+13\,\chi^{1/3}+\chi\tag{34}$$
--   gradient queries.
--   2. **Envelope (35).** For all $L_1,L_2>0$ and $\Phi_0\ge0$ there is $C>0$ such that for every instance of Assumption 5.1 with these constants and initial gap $\Phi_0$, and every $0<\varepsilon\le L_1^2/L_2$: running the model variant as above if $\chi\le(L_1^2/(L_2\varepsilon))^{3/4}$, and the gradient variant with the parameters of Theorem B.3 otherwise (each with $K=\max\{1,\lceil4\Phi_0/(DT\varepsilon)\rceil\}$), yields an $\varepsilon$-stationary output after at most
--   $$G_\varepsilon\le C\min\{\chi^{1/3}\varepsilon^{-3/2},\ \varepsilon^{-7/4}\}\tag{35}$$
--   gradient queries. In the dense case $\chi=d$.
--
--   The first part is the rolling-model rate; the envelope combines it with the first-order rate of Theorem B.3, the selection being made in advance from $\chi,L_1,L_2,\varepsilon$.
--
--   **Formalization Note** The theorem holds for every solver whose outputs are $\nu$-approximate solutions (31); the gradient variant never calls it. Counts are oracle calls, warm-up included.
--
--   Differences from the source:
--   - reading: (35) "for fixed L1, L2, Φ0, G_ε = O(min{χ^{1/3}ε^{−3/2}, ε^{−7/4}})" → ∀ L₁ L₂ > 0, ∀ Φ₀ ≥ 0, ∃ C > 0, uniformly in d, χ, f, x₀, the pattern, the partition and ε ∈ (0, L₁²/L₂]; reason: the proof on p. 32 bounds every term by constants depending on L₁, L₂, Φ₀ only (SUPPLEMENT.md decision 3)
--   - reading: "ν-approximate subproblem solutions" (not unique) → every solver satisfying IsNuSolver (outputs ν-approximate on every symmetric input, step-indexed); reason: every admissible choice of Δ_{n+1} is realized by such a solver (SUPPLEMENT.md decision 2)
--   - reading: "gradient queries" → the length of the run's oracle query list, with oracle locality; reason: base readings R3, R4
--   - encoding: k★ ∈ argmin_k ‖G_k‖ → the bounds for every minimizing k★; reason: ties are not broken by the paper
--   - encoding: i_n = ((n − 1) mod χ) + 1 → 0-based label (n − 1) % χ; partition with χ ≥ 1; reason: base readings R5, R7
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem 5.2, p. 21 (Theorem B.3, p. 31; envelope proof p. 32)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_OQN

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem 5.2 (RP-OQN: ε-stationarity with `O(χ^{1/3}ε^{−3/2} + χ)` gradients, and the envelope).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem 5.2, p. 21: "Let Assumption 5.1
hold, let `0 < ε ≤ L1²/L2`, and run the model variant of Algorithm 3 with `D = √(ε/(26 L2χ^{2/3}))`,
`η = 1/(2√3 χL2D)`, `T = ⌈(16√3 χ)^{1/3}⌉`, `ν ≤ ε/8`. Then for every `K ≥ 1`,
`‖∇f(w̄k★)‖ ≤ Φ0/(DKT) + 3/4 ε`, and with `K = max{1, ⌈4Φ0/(DTε)⌉}` the output is `ε`-stationary after
at most `Gε ≤ 62 Φ0 √L2 χ^{1/3}ε^{−3/2} + 13 χ^{1/3} + χ` (34) gradient queries. Running the model
variant if `χ ≤ (L1²/(L2ε))^{3/4}`, and the gradient variant with the parameters of Theorem B.3
otherwise, gives, for fixed `L1, L2, Φ0`, `Gε = O(min{χ^{1/3}ε^{−3/2}, ε^{−7/4}})`, (35) with `χ = d` in
the dense case."

Theorem B.3's parameters (p. 31): `D = ε^{3/4}/(9L₁^{1/2}L₂^{1/4})`, `η = 1/(√3L₁)`,
`T = ⌈(8√3L₁/(L₂D))^{1/3}⌉`. `Φ₀ = f(x₀) − inf f`. In both variants `K = max{1, ⌈4Φ₀/(DTε)⌉}`.

The statement has two parts.
1. For every instance of Assumption 5.1, every `0 < ε ≤ L₁²/L₂`, every `ν ≤ ε/8` and every solver
   returning ν-approximate subproblem solutions, the model variant with the stated parameters has
   oracle locality; satisfies `‖∇f(w̄_{k★})‖ ≤ Φ₀/(DKT) + 3ε/4` for every `K ≥ 1` and every minimizing
   `k★`; and with `K = max{1, ⌈4Φ₀/(DTε)⌉}` its output is ε-stationary for every minimizing `k★`, after
   at most (34) oracle calls.
2. (35): for all `L₁, L₂ > 0` and `Φ₀ ≥ 0` there is `C > 0` such that for every instance of
   Assumption 5.1 with these `L₁, L₂` and initial gap `Φ₀`, every `0 < ε ≤ L₁²/L₂`, every `ν ≤ ε/8` and
   every solver returning ν-approximate solutions for the model variant's parameters, the selected run
   (model variant if `χ ≤ (L₁²/(L₂ε))^{3/4}`, gradient variant otherwise, each with
   `K = max{1, ⌈4Φ₀/(DTε)⌉}`) outputs an ε-stationary point (every minimizing `k★`) using at most
   `C·min{χ^{1/3}ε^{−3/2}, ε^{−7/4}}` oracle calls.

**Formalization Note.** "For fixed `L1, L2, Φ0`" is read as `∀ L₁ L₂ Φ₀, ∃ C`, uniformly in `d`, `χ`,
`f`, `x₀`, `S`, the partition and `ε` (decision 3 of `SUPPLEMENT.md`). "`χ = d` in the dense case" is
the instance `S = [d] × [d]`, one column per group, which the statement covers. The ν-approximate
solutions are quantified over every solver satisfying `IsNuSolver`; the gradient variant never calls it.
Readings R3, R4 of the base mission: counts are oracle calls, warm-up included. -/
theorem theorem_5_2 :
    (∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ : ℝ) (S : Set (Fin d × Fin d))
      (grp : Fin d → Fin χ) (x₀ : EuclideanSpace ℝ (Fin d)) (ε ν : ℝ)
      (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
        Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Assumption51 d χ f L₁ L₂ S grp → 0 < ε → ε ≤ L₁ ^ 2 / L₂ → ν ≤ ε / 8 →
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
      (∀ kstar : ℕ,
        IsBestEpisode (fun n => (oqnRun cfg (gradient f) solver x₀ n).gw) T K₀ kstar →
        ‖gradient f (epAvg (fun n => (oqnRun cfg (gradient f) solver x₀ n).w) T kstar)‖ ≤ ε) ∧
      ((oqnAllQueries cfg (gradient f) solver x₀ (K₀ * T)).length : ℝ) ≤
        62 * Φ₀ * Real.sqrt L₂ * (χ : ℝ) ^ ((1 : ℝ) / 3) * ε ^ (-(3 : ℝ) / 2) +
          13 * (χ : ℝ) ^ ((1 : ℝ) / 3) + (χ : ℝ)) ∧
    (∀ L₁ L₂ : ℝ, 0 < L₁ → 0 < L₂ → ∀ Φ₀ : ℝ, 0 ≤ Φ₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (S : Set (Fin d × Fin d))
        (grp : Fin d → Fin χ) (x₀ : EuclideanSpace ℝ (Fin d)),
        Assumption51 d χ f L₁ L₂ S grp → f x₀ - ⨅ x, f x = Φ₀ →
        ∀ (ε ν : ℝ)
          (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
            Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          0 < ε → ε ≤ L₁ ^ 2 / L₂ → ν ≤ ε / 8 →
          let Dm : ℝ := Real.sqrt (ε / (26 * L₂ * (χ : ℝ) ^ ((2 : ℝ) / 3)))
          let ηm : ℝ := 1 / (2 * Real.sqrt 3 * (χ : ℝ) * L₂ * Dm)
          let Tm : ℕ := ⌈(16 * Real.sqrt 3 * (χ : ℝ)) ^ ((1 : ℝ) / 3)⌉₊
          let Km : ℕ := max 1 ⌈4 * Φ₀ / (Dm * (Tm : ℝ) * ε)⌉₊
          let cm : OQNConfig d χ := ⟨grp, S, Dm, ηm, true⟩
          let Dg : ℝ := ε ^ ((3 : ℝ) / 4) / (9 * L₁ ^ ((1 : ℝ) / 2) * L₂ ^ ((1 : ℝ) / 4))
          let ηg : ℝ := 1 / (Real.sqrt 3 * L₁)
          let Tg : ℕ := ⌈(8 * Real.sqrt 3 * L₁ / (L₂ * Dg)) ^ ((1 : ℝ) / 3)⌉₊
          let Kg : ℕ := max 1 ⌈4 * Φ₀ / (Dg * (Tg : ℝ) * ε)⌉₊
          let cg : OQNConfig d χ := ⟨grp, S, Dg, ηg, false⟩
          let env : ℝ := C * min ((χ : ℝ) ^ ((1 : ℝ) / 3) * ε ^ (-(3 : ℝ) / 2)) (ε ^ (-(7 : ℝ) / 4))
          IsNuSolver Dm ηm ν solver →
          ((χ : ℝ) ≤ (L₁ ^ 2 / (L₂ * ε)) ^ ((3 : ℝ) / 4) →
            (∀ kstar : ℕ,
              IsBestEpisode (fun n => (oqnRun cm (gradient f) solver x₀ n).gw) Tm Km kstar →
              ‖gradient f (epAvg (fun n => (oqnRun cm (gradient f) solver x₀ n).w) Tm kstar)‖ ≤ ε) ∧
            ((oqnAllQueries cm (gradient f) solver x₀ (Km * Tm)).length : ℝ) ≤ env) ∧
          ((L₁ ^ 2 / (L₂ * ε)) ^ ((3 : ℝ) / 4) < (χ : ℝ) →
            (∀ kstar : ℕ,
              IsBestEpisode (fun n => (oqnRun cg (gradient f) solver x₀ n).gw) Tg Kg kstar →
              ‖gradient f (epAvg (fun n => (oqnRun cg (gradient f) solver x₀ n).w) Tg kstar)‖ ≤ ε) ∧
            ((oqnAllQueries cg (gradient f) solver x₀ (Kg * Tg)).length : ℝ) ≤ env)) := by sorry

end RollingProbeQN.Convex.Supplement
