-- Prove2me | Theorems.Thm_SysBathGibbs_theorem_5_7
-- name    : SysBathGibbs.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:52.906197+00:00
-- url     : https://prove2.me/theorems/a1c4fa3e-d742-4eb6-8c99-16c0ad1434b3
-- title:
--   Theorem 5.7 — One-round approximation of $\Phi_{\alpha,T}$ by the ideal channel
-- statement:
--   There are constants $c_0,C>0$, depending only on $\beta$ and $q$, such that for $\sigma=\beta/2$, every chain (1.2) on $n\ge1$ sites, every real $\alpha$ with $n\alpha^2\sigma\le c_0$ and every $T\ge0$,
--   $$
--   \big\|\Gamma^{-1}(\Phi_{\alpha,T}-\tilde\Phi_{\alpha,T})\Gamma\big\|_{\rho_\beta\to\rho_\beta}\le C\big(n\alpha^4\sigma^2+n\alpha^2\sigma e^{-T^2/(8\sigma^2)}\big),
--   $$
--   where $\tilde\Phi_{\alpha,T}=\mathcal U(T)e^{\alpha^2\mathcal L}\mathcal U(T)$. Moreover, for every probability law $\mu$ of the interaction time supported on $[T_0,\infty)$, $T_0\ge0$, the averaged channels $\mathbb E_{T\sim\mu}\Phi_{\alpha,T}$ and $\mathbb E_{T\sim\mu}\tilde\Phi_{\alpha,T}$ satisfy the same bound with $T$ replaced by $T_0$.
--
--   The error is linear in $n$ at fourth order in $\alpha$, which is what allows parallel coupling with $\alpha^2=\Theta(\varepsilon/n)$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - encoding: "any common law of the interaction time supported on [T0, ∞)" → any probability measure μ on ℝ with μ(ℝ ∖ [T0, ∞)) = 0, for T0 ≥ 0; reason: interaction times are nonnegative; the law is otherwise arbitrary as on the page
--   - encoding: induced norm in ℝ → values in [0, ∞], compared with ofReal of the bound; reason: no junk value for the supremum
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Theorem 5.7 (eq. (5.18)), p.44

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Theorem 5.7 (One-round approximation)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.44.
There are `c₀, C > 0` depending only on `β, q` such that, for `σ = β/2`, every `T ≥ 0` and
`nα²σ ≤ c₀`, `‖Γ⁻¹(Φ_{α,T} - Φ̃_{α,T})Γ‖ ≤ C(nα⁴σ² + nα²σ e^{-T²/(8σ²)})`. For any common law of the
interaction time supported on `[T₀, ∞)`, the averaged channels satisfy the same bound with `T` replaced
by `T₀` on the right-hand side.

**Formalization Note.** `α` is any real number. A law is a probability measure on `ℝ` with
`μ([T₀, ∞)ᶜ) = 0`, for `T₀ ≥ 0`. -/
theorem theorem_5_7 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ α : ℝ, n * α ^ 2 * (β / 2) ≤ c₀ →
            (∀ T : ℝ, 0 ≤ T →
              kmsOpNorm β (chainHam h)
                  (onRelDens β (chainHam h) (roundChannel β h α T - idealRound β h α T)) ≤
                ENNReal.ofReal
                  (C * (n * α ^ 4 * (β / 2) ^ 2 +
                    n * α ^ 2 * (β / 2) * Real.exp (-T ^ 2 / (8 * (β / 2) ^ 2))))) ∧
            ∀ (μ : Measure ℝ) (T₀ : ℝ), IsProbabilityMeasure μ → 0 ≤ T₀ → μ (Set.Ici T₀)ᶜ = 0 →
              kmsOpNorm β (chainHam h)
                  (onRelDens β (chainHam h) (channelOf β h α μ - idealChannelOf β h α μ)) ≤
                ENNReal.ofReal
                  (C * (n * α ^ 4 * (β / 2) ^ 2 +
                    n * α ^ 2 * (β / 2) * Real.exp (-T₀ ^ 2 / (8 * (β / 2) ^ 2)))) := by sorry

end SysBathGibbs
