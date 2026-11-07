-- Prove2me | Theorems.Thm_QuadBogolyubov_proposition_D_9
-- name    : QuadBogolyubov.proposition_D_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:10:02.621605+00:00
-- url     : https://prove2.me/theorems/29b89a7e-2aa2-4c18-9245-4450356c44af
-- title:
--   Proposition D.9 — relative rooted cube counting lemma
-- statement:
--   There are absolute constants $C,K>0$ such that the following holds. Let $0<\eta\le1$ and let $W$ be a quadratic variety of complexity $(0,d)$, containing $0$, of rank $\mathrm{rk}(W)\ge C(d+\log_2(\eta^{-1}))$. For all 1-bounded $(F_\epsilon)_{\epsilon\in\mathcal V}$, with $\mathcal V=\{0,1\}^3\setminus\{(0,0,0)\}$, and every $\nu\in\mathcal V$,
--   $$|\Phi_W((F_\epsilon)_{\epsilon\in\mathcal V})|\le(1+K\eta)\|F_\nu\|_{U^3(W)}+K\eta,$$
--   and consequently
--   $$|\Phi_W((F_\epsilon)_{\epsilon\in\mathcal V})|\le(1+K\eta)\min_{\nu\in\mathcal V}\|F_\nu\|_{U^3(W)}+K\eta.$$
--   This is the rooted estimate from which Proposition 4.4 follows.
--
--   Differences from the source:
--   - reading: rk(W) ≥ C(d + log₂(η⁻¹)) with C unspecified; (1 + O(η))X; + O(η) → ∃ absolute C, K > 0 fixed before η, n, W and the functions; |· − X| ≤ KηX; + Kη; reason: the usual meaning of the O-notation and of the constant C in Appendix D
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: complexity (0, d), containing 0 → `W.d1 = 0` and `0 ∈ W.carrier`, with d = W.d2, without the normalization of (28); reason: the carrier, the forms β_j and the rank do not change under the normalization qⱼ ↦ qⱼ + qⱼ(0)
--   - encoding: min_{ν∈V} → `⨅` over the subtype {ν // ν ≠ 0}; reason: the infimum of a real family over a non-empty finite type is its minimum
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: 1-bounded family (F_ϵ)_{ϵ∈V}, V = {0,1}³ \ {0} → `F : (Fin 3 → ZMod 2) → 𝔽₂ⁿ → ℂ` with ‖F ν x‖ ≤ 1 for ν ≠ 0; the extra entry `F 0` is unconstrained and enters neither Φ_W nor the bounds; reason: Lean convention for a family indexed by V; the same instances
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition D.9, p.57

import Mathlib
import Definitions.Def_QuadBogolyubov_PhiW

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Proposition D.9 (Relative rooted cube counting lemma).** There are absolute constants
`C, K > 0` such that for every `0 < η ≤ 1` and every quadratic variety `W ∋ 0` of complexity
`(0, d)` with `rk(W) ≥ C(d + log₂(η⁻¹))`, all 1-bounded `(F_ε)_{ε∈V}`, `V = {0,1}³ \ {0}`, satisfy
`|Φ_W((F_ε))| ≤ (1 + Kη)‖F_ν‖_{U³(W)} + Kη` for every `ν ∈ V`, and consequently
`|Φ_W((F_ε))| ≤ (1 + Kη) min_{ν∈V} ‖F_ν‖_{U³(W)} + Kη`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition D.9, p.57: "Let 0 < η ≤ 1, and let W be a quadratic variety of complexity (0, d)
and rank rk(W) ≥ C(d + log2(η⁻¹)) containing 0. Then for all 1-bounded functions (Fϵ)ϵ∈V and
every ν ∈ V |ΦW((Fϵ)ϵ∈V)| ≤ (1 + O(η))∥Fν∥U3(W) + O(η). Consequently,
|ΦW((Fϵ)ϵ∈V)| ≤ (1 + O(η)) min_{ν∈V} ∥Fν∥U3(W) + O(η)."

**Formalization Note.** `C` is the sufficiently large absolute constant of Appendix D and the
`O(η)` terms are `K η` with `K` absolute; both are fixed before `η`, `n`, `d`, `W` and `F`. The
family is `F : (Fin 3 → ZMod 2) → 𝔽₂ⁿ → ℂ`, bounded by `1` for `ν ≠ 0` (`F 0` does not enter).
`min_{ν∈V}` is `⨅` over the subtype `{ν // ν ≠ 0}`. -/
theorem proposition_D_9 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (n : ℕ) (W : QuadVariety n),
        W.d1 = 0 → (0 : Fin n → ZMod 2) ∈ W.carrier →
        HasRankAtLeast W (C * ((W.d2 : ℝ) + Real.logb 2 η⁻¹)) →
        ∀ F : (Fin 3 → ZMod 2) → (Fin n → ZMod 2) → ℂ,
          (∀ ν, ν ≠ 0 → ∀ x, ‖F ν x‖ ≤ 1) →
          (∀ ν, ν ≠ 0 → ‖PhiW W F‖ ≤ (1 + K * η) * localU3 W (F ν) + K * η) ∧
          ‖PhiW W F‖ ≤
            (1 + K * η) * (⨅ ν : {ν : Fin 3 → ZMod 2 // ν ≠ 0}, localU3 W (F ν)) + K * η := by sorry

end QuadBogolyubov
