-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_7_4
-- name    : SparseSDP.TwoSided.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:54.121205+00:00
-- url     : https://prove2.me/theorems/32c5dc9a-ed6e-48de-967c-1f46cf66823b
-- title:
--   Lemma 7.4, p. 50 — Lánczos is accurate along the whole trajectory
-- statement:
--   Consider a run of Algorithm 7 with $C_L$ sufficiently large. With probability at least $1-\delta_L$, where $\delta_L=\delta/3$, every computed projector is within trace distance $1/T$ of its exact counterpart:
--   $$
--   \|\tilde\rho_t-\rho_t\|_1\le\frac1T\quad\text{for all }t\in[T].
--   $$
--
--   The trajectory is adaptive, so the comparison is made round by round on the realized Hamiltonian $H_t$.
--
--   Differences from the source:
--   - reading: $C_L$ a sufficiently large universal constant → $\exists C_0$, for all `Consts` with $C_0\le C_L$; reason: the meaning of the phrase
--   - encoding: $\|\cdot\|_1$ → the published `WildeQIT.traceNorm` of the matrix mapped to $\mathbb C$; reason: same norm, no factor $\tfrac12$
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 7.4, p. 50, Eq. (249)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Lemma 7.4** (Uniform Lánczos Accuracy Along Sampled Trajectory), p. 50.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 7.4, p. 50.

`ρ̃_t` is `rhoTil`, `ρ_t` is `rhoEx` with `η = η_X`, and `‖·‖₁` is the published `traceNorm`, applied
to the real matrix mapped to `ℂ`. The failure probability is bounded by `δ_L = δ/3`, for `C_L`
sufficiently large. -/
theorem lemma_7_4 : ∃ C₀ : ℝ, ∀ (P : Consts), C₀ ≤ P.CL →
    ∀ {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d) (acc : RowAccess d k) (s : ℕ)
      (c ω R r δ : ℝ) (T : ℕ), Alg7Hyp M acc s c ω R r δ → 1 ≤ T →
      tapeLaw {tape | ¬ ∀ p ∈ (traj P acc s ω R r T δ tape).zipIdx,
        WildeQIT.traceNorm ((rhoTil p.1 - rhoEx M r (etaX d T r ω) (traj P acc s ω R r T δ tape)
          p.2 p.1).map (fun x : ℝ => (x : ℂ))) ≤ 1 / (T : ℝ)} ≤
        ENNReal.ofReal (δ / 3) := by sorry

end SparseSDP.TwoSided
