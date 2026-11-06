-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_7_9
-- name    : SparseSDP.TwoSided.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:57.951821+00:00
-- url     : https://prove2.me/theorems/3d6962f0-b364-4688-a55d-fda9943f3bb6
-- title:
--   Lemma 7.9, p. 58 — pure-constraint sampling
-- statement:
--   In a run of Algorithm 7, for every $\delta_S\in(0,1)$, with probability at least $1-\delta_S$,
--   $$
--   r\sum_{t=1}^T\big([\tilde c_t]_{J_t}-\langle\tilde c_t,\hat p_t\rangle\big)\le2Rr\omega\sqrt{2T\log\frac1{\delta_S}}.
--   $$
--
--   Playing one sampled constraint instead of the mixture adds only a martingale fluctuation.
--
--   Differences from the source:
--   - generalization: Algorithm 7 with its parameters → every `Consts`; reason: the proof does not use the constants of the algorithm
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 7.9, p. 58, Eq. (321)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Lemma 7.9** (Pure-Constraint Sampling), p. 58.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 7.9, p. 58.

`[c̃_t]ⱼ = ⟨Aⱼ, X̃_t⟩` (Eq. (231)) and `p̂_t` is the distribution of line 8. -/
theorem lemma_7_9 (P : Consts) {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d)
    (acc : RowAccess d k) (s : ℕ) (c ω R r δ δS : ℝ) (T : ℕ)
    (hyp : Alg7Hyp M acc s c ω R r δ) (hT : 1 ≤ T) (hδ0 : 0 < δS) (hδ1 : δS < 1) :
    tapeLaw {tape | ¬ r * ((traj P acc s ω R r T δ tape).map fun x =>
          cTil M R x x.J - cTil M R x ⬝ᵥ x.p).sum ≤
        2 * R * r * ω * √(2 * T * Real.log (1 / δS))} ≤
      ENNReal.ofReal δS := by sorry

end SparseSDP.TwoSided
