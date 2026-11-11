-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_filter_simulation
-- name    : SingleCopyMoments.Adaptive.filter_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:47:13.200214+00:00
-- url     : https://prove2.me/theorems/d7ffdfc3-8d73-49dd-afe3-e645fbe111ec
-- title:
--   Lemma 23 — Single-copy simulation after filtering
-- statement:
--   Let $K$ be a known contraction, let $s_0>0$, let $\beta\in(0,1)$, and fix any inner adaptive single-copy protocol using $N\ge1$ copies. One simulator, chosen independently of the unknown input state, uses the fixed budget
--
--   $$M=\left\lceil\frac8{s_0}\left(N+\log\frac1\beta\right)\right\rceil.$$
--
--   For every state $\rho$ with $s=\operatorname{Tr}(K\rho K^\dagger)\ge s_0$, its completed decoded transcript has exactly the law of the inner protocol on $\sigma=K\rho K^\dagger/s$, with completion probability at least $1-\beta$. The equality includes the inner seed. Exhaustion is a measurable failure event and all original attempts count toward $M$.
--
--   This preserves arbitrary adaptation with only classical information between copies. In measure notation the decoded successful submeasure is $q$ times the intended law for some $q\in[1-\beta,1]$.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: simulate the successful transcript with additional failure at most beta → equality of the decoded completion submeasure to q times the inner transcript law, with q at least 1-beta; reason: constant per-attempt success is independent of the inner history and seed, so completion preserves its exact transcript law
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 23, printed p. 25 (PDF p. 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Pilot

open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 23, printed p.25 (PDF p.27). One simulator is chosen before the input state. -/
theorem filter_simulation (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    (K : Op d) (hK : Loewner (K.conjTranspose * K) 1)
    (s₀ β : ℝ) (hs : 0 < s₀) (hβ : β ∈ Set.Ioo 0 1) (P : Protocol d) :
    ∃ Q : Protocol d, ∃ decode : Record Q → Record P, ∃ good : Set (Record Q),
      Simulates K s₀ β P Q N ⌈(8/s₀) * ((N : ℝ) + Real.log (1/β))⌉₊ decode good := by sorry

end SingleCopyMoments.Adaptive
