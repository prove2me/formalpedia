-- Prove2me | Theorems.Thm_PersuadeFly_lemma_2
-- name    : PersuadeFly.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:32:39.721885+00:00
-- url     : https://prove2.me/theorems/e49afc46-343b-41bd-ad95-5005e6fc147f
-- title:
--   Lemma 2, p.39 — the regret decomposition of Rai
-- statement:
--   Let $\sigma[h_t]$ be a run of the Rai algorithm with parameters $\gamma_0$, $\mathcal C_0$, $(\epsilon_t)$ and horizon $T$, and let $\mu^*\in\Delta(\Omega)$. Write $\gamma_t$ and $\mathcal B_t$ for the estimate and the confidence set after the history $h_t$. Then on every path $(\omega_t,a_t)_{t\in[T]}$,
--   $$
--   \begin{aligned}
--   \mathsf{Reg}_{\mathcal I}(\mathfrak{Rai},\mu^*,T)\le{}&\sum_{t\in[T]}\mathsf{Gap}\big(\mu^*,\mathsf B_1(\mu^*,\|\mu^*-\gamma_t\|_1)\big)+\sum_{t\in[T]}\mathsf{Gap}(\gamma_t,\mathcal B_t)\\
--   &+\sum_{t\in[T]}\|\mu^*-\gamma_t\|_1+\sum_{t\in[T]}\big(V(\mu^*,\sigma[h_t])-v(\omega_t,a_t)\big).
--   \end{aligned}
--   $$
--   Here $V(\mu^*,\sigma[h_t])=\mathbf E_{\mu^*}[v(\omega_t,a_t)\mid h_t]$. The regret splits into the cost of robustness at the truth, the cost of robustness at the estimate, an estimation error, and a martingale term; the regret bound of Theorem 2 bounds each of the four sums.
--
--   Differences from the source:
--   - generalization: Rai with the radii ϵ_t of Theorem 2 and μ* ∈ B₀ → any radius sequence (ϵ_t) and any μ* ∈ Δ(Ω); reason: the decomposition uses neither the radii nor μ* ∈ B₀; Theorem 2's choice is an instance
--   - generalization: first confidence set: B₀ (Algorithm 1's box) or B₁(γ₀, ϵ₀) = Δ(Ω) (text of p.20 and the proofs) → any set C₀ with B₀ ⊆ C₀ ⊆ Δ(Ω); reason: both readings are instances of C₀
--   - encoding: E_{μ*}[v(ω_t, a_t) | h_t] → V(μ*, σ[h_t]); reason: the identity stated on p.39; a verification file checks it against the path law
--   - encoding: history h_t = ∪_{τ<t}{(τ, ω_τ, a_τ, â_τ)} → the first t pairs (ω_τ, a_τ) of the path, a function Fin t → Ω × A; reason: â_τ = a_τ under robust persuasiveness (p.19); [T] = {0, …, T−1} is Fin T
--   - encoding: OPT(μ) = max_σ V(μ, σ) subject to σ ∈ Pers(μ) → the supremum of V(μ, ·) over Pers(μ); reason: the maximum is attained (compact nonempty polytope), so the two values coincide; p.23 writes the sup
--   - encoding: an inequality between random variables → the inequality on every path (ω_t, a_t)_{t ∈ [T]}; reason: the source's inequality is pathwise; nothing is lost on null paths
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 2, p.39

import Mathlib
import Definitions.Def_PersuadeFly_IsRai
import Definitions.Def_PersuadeFly_gap
import Definitions.Def_PersuadeFly_regret
import Definitions.Def_PersuadeFly_historyAt

namespace PersuadeFly

/-- **Lemma 2 (regret decomposition).** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 2, p.39: the Rai algorithm satisfies
`Reg(Rai, μ*, T) ≤ ∑_{t ∈ [T]} Gap(μ*, B₁(μ*, ‖μ* − γ_t‖₁)) + ∑_{t ∈ [T]} Gap(γ_t, B_t)
  + ∑_{t ∈ [T]} ‖μ* − γ_t‖₁ + ∑_{t ∈ [T]} (E_{μ*}[v(ω_t, a_t) | h_t] − v(ω_t, a_t))`.

The inequality holds on every path `(ω_t, a_t)_{t ∈ [T]}`.

**Formalization Note** `E_{μ*}[v(ω_t, a_t) | h_t]` is written `V(μ*, σ[h_t])`, the identity used in the
proof (p.39). The statement is for every radius sequence `ε` and every `μ* ∈ Δ(Ω)` (the paper's
setting: Theorem 2's `ϵ_t` and `μ* ∈ B₀`). -/
theorem lemma_2 {Ω A : Type} [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (γ0 : Ω → ℝ) (C0 : Set (Ω → ℝ)) (ε : ℕ → ℝ) (T : ℕ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) (hRai : IsRai I γ0 C0 ε T alg)
    (μ : Ω → ℝ) (hμ : μ ∈ stdSimplex ℝ Ω) (path : Fin T → Ω × A) :
    regret I μ T path ≤
      ∑ t : Fin T, gap I μ (ball1 μ (l1Dist μ (raiEmpirical γ0 t (historyAt path t)))) +
      ∑ t : Fin T, gap I (raiEmpirical γ0 t (historyAt path t)) (raiSet γ0 C0 ε t (historyAt path t)) +
      ∑ t : Fin T, l1Dist μ (raiEmpirical γ0 t (historyAt path t)) +
      ∑ t : Fin T, (value I μ (alg t (historyAt path t)) - I.v (path t).1 (path t).2) := by sorry

end PersuadeFly
