-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_6_4
-- name    : PolymerEndpoint.Atomic.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:33.359137+00:00
-- url     : https://prove2.me/theorems/c6ee87d1-f13c-4204-8a1c-483cf1a1ccaa
-- title:
--   Lemma 6.4 — semicontinuous Dini theorem
-- statement:
--   Let $\mathcal X$ be a compact metric space. Suppose $(F_n)$ is a nondecreasing sequence of lower semicontinuous real-valued functions on $\mathcal X$ and converges pointwise to an upper semicontinuous function $F$. Then
--   $$
--   \sup_{x\in\mathcal X}|F_n(x)-F(x)|\longrightarrow0.
--   $$
--
--   This uniform convergence principle applies to the threshold functionals in the compact partitioned-state space.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 43, Lemma 6.4

import Mathlib

open Filter
open scoped Topology

namespace PolymerEndpoint.Atomic

theorem lemma_6_4 {𝒳 : Type*} [MetricSpace 𝒳] [CompactSpace 𝒳]
    (F : ℕ → 𝒳 → ℝ) (G : 𝒳 → ℝ)
    (hmono : Monotone F)
    (hF : ∀ n, LowerSemicontinuous (F n))
    (hG : UpperSemicontinuous G)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    TendstoUniformly F G atTop := by sorry

end PolymerEndpoint.Atomic
