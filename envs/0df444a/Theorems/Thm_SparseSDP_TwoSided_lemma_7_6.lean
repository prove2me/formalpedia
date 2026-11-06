-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_7_6
-- name    : SparseSDP.TwoSided.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:56.64145+00:00
-- url     : https://prove2.me/theorems/f7f8b792-7e99-4e1f-b996-0e0b396d5624
-- title:
--   Lemma 7.6, p. 52 — the rank-one sampling error
-- statement:
--   In a run of Algorithm 7, for every $\delta_X\in(0,1)$, with probability at least $1-\delta_X$,
--   $$
--   \sum_{t=1}^T\langle G_t,\bar X_t-X_t\rangle\le2Rr\omega\sqrt{2T\log\frac1{\delta_X}}.
--   $$
--
--   The difference $\bar X_t-X_t$ is the cost of playing one fresh rank-one sample instead of its mean.
--
--   Differences from the source:
--   - generalization: Algorithm 7 with its parameters → every `Consts`; reason: the proof does not use the constants of the algorithm
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 7.6, p. 52, Eq. (267)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Lemma 7.6** (Rank-one response sampling), p. 52.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 7.6, p. 52.

`G_t = r A_{J_t}`, `X̄_t = R P̄(η_X H_t)` (Eq. (248)) and `X_t = Rρ_t` (Eq. (246)). -/
theorem lemma_7_6 (P : Consts) {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d)
    (acc : RowAccess d k) (s : ℕ) (c ω R r δ δX : ℝ) (T : ℕ)
    (hyp : Alg7Hyp M acc s c ω R r δ) (hT : 1 ≤ T) (hδ0 : 0 < δX) (hδ1 : δX < 1) :
    tapeLaw {tape | ¬ sumR (traj P acc s ω R r T δ tape) (fun t x =>
        hs (gain M r x) (Xmean M R r (etaX d T r ω) (traj P acc s ω R r T δ tape) t -
          R • rhoEx M r (etaX d T r ω) (traj P acc s ω R r T δ tape) t x)) ≤
        2 * R * r * ω * √(2 * T * Real.log (1 / δX))} ≤
      ENNReal.ofReal δX := by sorry

end SparseSDP.TwoSided
