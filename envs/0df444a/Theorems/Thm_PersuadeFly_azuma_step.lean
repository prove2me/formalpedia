-- Prove2me | Theorems.Thm_PersuadeFly_azuma_step
-- name    : PersuadeFly.azuma_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:01.728042+00:00
-- url     : https://prove2.me/theorems/8eb5e608-f243-4026-9f9b-eb407f5c77a5
-- title:
--   Proof of Theorem 2, p.38 — the Azuma–Hoeffding tail of the martingale term (corrected: $\le$ for the printed $<$)
-- statement:
--   Let a signaling algorithm $\sigma[h_t]$ and $\mu^*\in\Delta(\Omega)$ be given, let $T\ge1$, and let $X_t=V(\mu^*,\sigma[h_t])-v(\omega_t,a_t)$, where $V(\mu^*,\sigma[h_t])=\mathbf E_{\mu^*}[v(\omega_t,a_t)\mid h_t]$. For every $z\ge0$,
--   $$
--   \mathbf P_{\mu^*}\Big(\sum_{t\in[T]}X_t\ge z\Big)\le\exp\Big(-\frac{2z^2}{T}\Big).
--   $$
--   The $X_t$ are bounded martingale differences, and this is the Azuma–Hoeffding step that turns the martingale term of the regret decomposition into the failure probability $T^{-8\Phi|\Omega|}$ of Theorem 2.
--
--   Differences from the source:
--   - correction: P_{μ*}(∑ X_t ≥ z) < exp(−2z²/T) for z ≥ 0 → ≤; reason: the strict form is false: with v ≡ 0 and z = 0 both sides equal 1, and this instance meets every assumption
--   - generalization: the Rai algorithm and μ* ∈ B₀ → any signaling algorithm and any μ* ∈ Δ(Ω); reason: the step uses only that X_t is a martingale difference with conditional range 1; Rai is an instance
--   - encoding: E_{μ*}[v(ω_t, a_t) | h_t] → V(μ*, σ[h_t]); reason: the identity stated on p.39; a verification file checks it against the path law
--   - encoding: history h_t = ∪_{τ<t}{(τ, ω_τ, a_τ, â_τ)} → the first t pairs (ω_τ, a_τ) of the path, a function Fin t → Ω × A; reason: â_τ = a_τ under robust persuasiveness (p.19); [T] = {0, …, T−1} is Fin T
--   - encoding: a time horizon of length T → T ≥ 1; reason: nondegeneracy: [T] is nonempty
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, proof of Theorem 2, p.38, "Hence, from Azuma-Hoeffding"

import Mathlib
import Definitions.Def_PersuadeFly_IsSignalingAlgorithm
import Definitions.Def_PersuadeFly_pathEventProb
import Definitions.Def_PersuadeFly_value

namespace PersuadeFly

/-- **The Azuma–Hoeffding step of the proof of Theorem 2** (corrected: `≤` for the printed `<`).
Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, proof of Theorem 2, p.38, "Hence, from Azuma-Hoeffding": with
`X_t = E_{μ*}[v(ω_t, a_t) | h_t] − v(ω_t, a_t)`, for `z ≥ 0`,
`P_{μ*}(∑_{t ∈ [T]} X_t ≥ z) ≤ exp(−2z²/T)`.

**Formalization Note** The page prints `<`, which fails at `z = 0` when `v ≡ 0` (both sides are 1).
`E_{μ*}[v(ω_t, a_t) | h_t]` is `V(μ*, σ[h_t])` (p.39). The step holds for every signaling algorithm. -/
theorem azuma_step {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (T : ℕ) (hT : 1 ≤ T) (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) (halg : IsSignalingAlgorithm T alg)
    (μ : Ω → ℝ) (hμ : μ ∈ stdSimplex ℝ Ω) (z : ℝ) (hz : 0 ≤ z) :
    pathEventProb μ alg T
        {path | z ≤ ∑ t : Fin T, (value I μ (alg t (historyAt path t)) - I.v (path t).1 (path t).2)} ≤
      Real.exp (-(2 * z ^ 2 / T)) := by sorry

end PersuadeFly
