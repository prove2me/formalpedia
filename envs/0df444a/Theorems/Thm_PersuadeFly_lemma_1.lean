-- Prove2me | Theorems.Thm_PersuadeFly_lemma_1
-- name    : PersuadeFly.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:02.753474+00:00
-- url     : https://prove2.me/theorems/7fdf269e-094f-4b65-8199-56268492ed01
-- title:
--   Lemma 1, p.33 — $\ell_1$ concentration of the empirical distribution
-- statement:
--   Let $\mu\in\Delta(\Omega)$, let $t\in\mathbb N$, and let $\gamma_t$ be the empirical distribution of $t$ independent draws from $\mu$. For all $0<\Phi_t\le2\sqrt t$,
--   $$
--   \mathbf P_\mu\Big(\|\gamma_t-\mu\|_1\ge\sqrt{\frac{|\Omega|}{t}}\,(1+\Phi_t)\Big)\le\exp\Big(-\frac{3\Phi_t^2\sqrt{|\Omega|}}{56}\Big)\,\mathbf I\Big\{\sqrt{\frac{|\Omega|}{t}}\,(1+\Phi_t)\le2\Big\}.
--   $$
--   The empirical distribution concentrates around $\mu$ in $\ell_1$ at rate $\sqrt{|\Omega|/t}$. This is what makes the confidence sets of Rai contain $\mu^*$ with high probability (Theorem 1).
--
--   Differences from the source:
--   - encoding: for each t ∈ [T] → for every t ∈ ℕ; reason: every t lies in [T] for some T, and the hypothesis 0 < Φ_t ≤ 2√t forces t ≥ 1
--   - encoding: P_μ, the law of the states → the iid product law of (ω_τ)_{τ<t}; reason: a verification file shows it is the state marginal of the path law
--   - encoding: √Ω, log T, T^x → √|Ω|, the natural logarithm Real.log, Real.rpow; reason: √Ω means √|Ω| (the proof of Lemma 1 has 3Φ²t|Ω|, p.34); the proofs use exp(−c log T) = T^{−c}
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 1, p.33

import Mathlib
import Definitions.Def_PersuadeFly_iidEventProb
import Definitions.Def_PersuadeFly_empiricalDist
import Definitions.Def_PersuadeFly_l1Dist

namespace PersuadeFly

/-- **Lemma 1 (ℓ₁ concentration of the empirical distribution).** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 1, p.33: for each
`t ∈ [T]` and any `μ ∈ Δ(Ω)`, for all `0 < Φ_t ≤ 2√t`,
`P_μ(‖γ_t − μ‖₁ ≥ √(|Ω|/t) (1 + Φ_t)) ≤ exp(−3Φ_t²√|Ω| / 56) · I{√(|Ω|/t) (1 + Φ_t) ≤ 2}`,
where `γ_t` is the empirical distribution of `t` iid draws from `μ`.

**Formalization Note** `√Ω` in the exponent is `√|Ω|` (the proof, p.34, has `3Φ_t²√|Ω|`). The law is
the iid product law of `(ω_τ)_{τ<t}`; the hypothesis `0 < Φ_t ≤ 2√t` forces `t ≥ 1`. -/
theorem lemma_1 {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω]
    (μ : Ω → ℝ) (hμ : μ ∈ stdSimplex ℝ Ω) (t : ℕ) (Φt : ℝ) (hΦ0 : 0 < Φt)
    (hΦ1 : Φt ≤ 2 * Real.sqrt t) :
    iidEventProb μ t {s | Real.sqrt ((Fintype.card Ω : ℝ) / t) * (1 + Φt) ≤ l1Dist (empiricalDist t s) μ} ≤
      Real.exp (-(3 * Φt ^ 2 * Real.sqrt (Fintype.card Ω) / 56)) *
        (if Real.sqrt ((Fintype.card Ω : ℝ) / t) * (1 + Φt) ≤ 2 then 1 else 0) := by sorry

end PersuadeFly
