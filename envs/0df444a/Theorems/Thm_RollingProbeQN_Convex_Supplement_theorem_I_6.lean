-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_I_6
-- name    : RollingProbeQN.Convex.Supplement.theorem_I_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:47:41.45467+00:00
-- url     : https://prove2.me/theorems/d2d1d454-57dc-4222-96b8-532b6871e5ea
-- title:
--   Theorem I.6 — master formula: $\|\nabla f(\bar w_{k^\star})\|\le\Phi_0/(DN)+2\nu+13\,\omega^{2/3}L_2D^2$
-- statement:
--   Let $f$ satisfy Assumption 5.1 and write $\Phi_0=f(x_0)-\inf f$. Let $D>0$, $\omega\ge1$ and $\Gamma\le\omega L_2D$, and run the conversion with the optimistic learner: increments $\Delta_n$ ($\Delta_0=0$), symmetric matrices $B_n$, and $\Delta_{n+1}$ a $\nu$-approximate solution of the subproblem at step $n$ for every $n$, with
--   $$\eta=\frac1{2\sqrt3\,\omega L_2D},\qquad T=\big\lceil(16\sqrt3\,\omega)^{1/3}\big\rceil .$$
--   Assume the certificate (32): $\|\theta_{n+1}\|\le\Gamma\|\Delta_{n+1}-\Delta_n\|$ for every step $n$ of the run. Then:
--
--   1. $T\le4.1\,\omega^{1/3}$ (for every $\omega\ge1$);
--   2. for every $K\ge1$, $N=KT$, and every episode $k^\star$ minimizing $\|G_k\|$ over $1\le k\le K$,
--   $$\|\nabla f(\bar w_{k^\star})\|\le\frac{\Phi_0}{DN}+2\nu+13\,\omega^{2/3}L_2D^2.\tag{86}$$
--
--   This is the master formula from which Theorems 5.2, B.3 and I.9 follow by choosing $D$ and the certificate: a pointwise hint certificate $\Gamma\le\omega L_2D$ costs a factor $\omega^{1/3}$ in the iteration count.
--
--   **Formalization Note** The conversion is a predicate on arbitrary sequences $B_n$, $\Delta_n$, so every symmetric model and every admissible choice of approximate solutions is covered; for a given $K$ it, and the certificate (32), are required only at the steps $n<N=KT$ of the run. Gradients are exact and no oracle count is claimed. $\inf f$ is finite because $f$ is bounded below.
--
--   Differences from the source:
--   - generalization: B_n symmetric, Δ_{n+1} ν-approximate and the certificate (32) for every n ≥ 0 → for each K, these conditions only at the steps n < N = KT; reason: the bound concerns the first N steps only; the paper's "for every n ≥ 0" implies the Lean hypotheses, so the Lean statement specializes to the paper's
--   - encoding: "run the conversion with the optimistic learner, ν-approximate subproblem solutions" → a predicate on arbitrary sequences B, Δ: Δ₀ = 0, B_n symmetric, Δ_{n+1} a ν-approximate solution (31) at step n; reason: every realized run is such a pair of sequences, and conversely
--   - encoding: radius D of the learner → hypothesis 0 < D; reason: the paper takes D > 0 (p. 71, Lemma I.3)
--   - encoding: k★ ∈ argmin_k ‖G_k‖ → (86) for every minimizing k★; reason: ties are not broken by the paper
--   - encoding: partition g_1, …, g_χ of [d] in Assumption 5.1 → 0 < χ and a surjective 0-based group map; reason: base reading R7
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem I.6, p. 73 (certificate (32), p. 19; conversion (23)–(31), pp. 18–19; proof pp. 73–74)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_Conversion

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem I.6 (master formula for the conversion with the optimistic learner).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem I.6, p. 73: "Let Assumption 5.1
hold, let the symmetric matrices `Bn` satisfy the certificate (32) with `Γ ≤ ωL2D` for some `ω ≥ 1`,
and run the conversion with the optimistic learner, `ν`-approximate subproblem solutions, and
`η = 1/(2√3 ωL2D)`, `T = ⌈(16√3 ω)^{1/3}⌉ ≤ 4.1 ω^{1/3}`. Then for every `K ≥ 1` and `N = KT`,
`‖∇f(w̄k★)‖ ≤ Φ0/(DN) + 2ν + 13 ω^{2/3}L2D²`. (86)"

The certificate (32), p. 19: `‖θ_{n+1}‖ ≤ Γ‖Δ_{n+1} − Δ_n‖` for every `n ≥ 0`. `Φ₀ = f(x₀) − inf f`
(p. 18). The conversion (23)–(31): increments `Δ_n` with `Δ_0 = 0`, `x_n = x_{n−1} + Δ_n`,
`w_n = x_{n−1} + Δ_n/2`, `z_n = x_n + Δ_n/2`, `θ_0 = 0`,
`θ_{n+1} = ∇f(w_{n+1}) − ∇f(z_n) − B_n(Δ_{n+1} − Δ_n)/2`, `Δ_{n+1}` a ν-approximate solution of the
subproblem at step `n`; episodes `N_k = {(k−1)T + 1, …, kT}`, `G_k = ∑_{n∈N_k} ∇f(w_n)`,
`w̄_k = (1/T)∑_{n∈N_k} w_n`, and `k★` minimizes `‖G_k‖` over `1 ≤ k ≤ K`.

The statement has two parts: `T ≤ 4.1ω^{1/3}` for every `ω ≥ 1`; and (86) for every `K ≥ 1`, every
run of `N = KT` iterations satisfying the certificate at its steps `n < N`, and every minimizing `k★`.

**Formalization Note.** The run is the predicate `IsOptimisticRun` on arbitrary sequences `B`, `Δ`
(so every choice of approximate solutions and every symmetric model is covered), required, with the
certificate (32), only at the steps `n < N` of the run; the paper's "for every `n ≥ 0`" implies it. `D > 0` is the radius
of the learner's ball (p. 71: "where `D > 0`"). Gradients here are exact (`∇f`), as in the paper's
conversion; no oracle count is claimed. -/
theorem theorem_I_6 :
    (∀ ω : ℝ, 1 ≤ ω →
      ((⌈(16 * Real.sqrt 3 * ω) ^ ((1 : ℝ) / 3)⌉₊ : ℕ) : ℝ) ≤ 4.1 * ω ^ ((1 : ℝ) / 3)) ∧
    ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ : ℝ) (S : Set (Fin d × Fin d))
      (grp : Fin d → Fin χ) (x₀ : EuclideanSpace ℝ (Fin d)) (D ν Γ ω : ℝ)
      (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (Δ : ℕ → EuclideanSpace ℝ (Fin d)),
      Assumption51 d χ f L₁ L₂ S grp → 0 < D → 1 ≤ ω → Γ ≤ ω * L₂ * D →
      let η : ℝ := 1 / (2 * Real.sqrt 3 * ω * L₂ * D)
      let T : ℕ := ⌈(16 * Real.sqrt 3 * ω) ^ ((1 : ℝ) / 3)⌉₊
      ∀ K : ℕ, 1 ≤ K →
      IsOptimisticRun f x₀ D η ν B Δ (K * T) →
      (∀ n < K * T, ‖convTheta f B x₀ Δ (n + 1)‖ ≤ Γ * ‖Δ (n + 1) - Δ n‖) →
      ∀ kstar : ℕ,
        IsBestEpisode (fun n => gradient f (convW x₀ Δ n)) T K kstar →
        ‖gradient f (epAvg (convW x₀ Δ) T kstar)‖ ≤
          (f x₀ - ⨅ x, f x) / (D * ((K : ℝ) * (T : ℝ))) + 2 * ν +
            13 * ω ^ ((2 : ℝ) / 3) * L₂ * D ^ 2 := by sorry

end RollingProbeQN.Convex.Supplement
