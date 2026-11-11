-- Prove2me | Theorems.Thm_PetzMix_corollary_3_5
-- name    : PetzMix.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:55.656065+00:00
-- url     : https://prove2.me/theorems/ff782904-0b5f-4602-80d0-ef29540ccfe2
-- title:
--   Corollary 3.5 — summable $\eta$ implies rapid mixing
-- statement:
--   Under the assumptions of Theorem 3.4 (with $\gamma_\ell=1-a_\eta/\ell>0$):
--
--   1. the Gibbs state $\sigma_\beta$ is the unique stationary state of $e^{t\mathcal L_\ell}$: a state $\sigma'$ satisfies $e^{t\mathcal L_\ell}\sigma'=\sigma'$ for all $t\ge0$ if and only if $\sigma'=\sigma_\beta$;
--   2. for every state $\rho$ and every $t\ge0$,
--   $$
--   \tfrac12\|e^{t\mathcal L_\ell}(\rho)-\sigma_\beta\|_1\le n\,e^{-\gamma_\ell t};
--   $$
--   3. for every $\varepsilon>0$,
--   $$
--   t_{\mathrm{mix}}(\varepsilon)\le\frac1{\gamma_\ell}\log\frac n\varepsilon,\qquad t_{\mathrm{mix}}(\varepsilon)=\inf\big\{t\ge0:\tfrac12\|e^{t\mathcal L_\ell}(\rho)-\sigma_\beta\|_1\le\varepsilon\ \forall\rho\big\}.
--   $$
--
--   This turns $W_1$ curvature into a trace-distance mixing bound with logarithmic dependence on the system size.
--
--   **Formalization Note** The public mixing time `tmix L σ ε` uses $\|\cdot\|_1\le\varepsilon$ without the factor $\tfrac12$, so the paper's $t_{\mathrm{mix}}(\varepsilon)$ is `tmix L σ (2ε)`. The bound is in $[0,\infty]$ and its right side is truncated at $0$ (for $\varepsilon\ge n$ the mixing time is $0$).
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: B ∈ B_{n,ℓ}, the cyclic intervals of length ℓ, with 1 ≤ ℓ < n → cycBlock ℓ s for s : Fin n, 1 ≤ ℓ < n; reason: the n blocks are indexed by their left ends and are distinct for 1 ≤ ℓ < n
--   - encoding: a summable decay function, a_η = 2Σ_{r≥1} η(r) < ∞ → Summable (fun r => η (r + 1)) with aEta η = 2 * ∑' r, η (r + 1); reason: a real tsum of a divergent series is 0, so convergence is stated explicitly
--   - reading: Definition 3.1 for every observable A → HasExtInfluence quantifies over Hermitian A; reason: the paper's usage: 'observable A = A†' (p.16); this weakens the hypothesis
--   - encoding: t_mix(ε) with ½‖·‖₁ ≤ ε → tmix L σ (2 * ε); reason: QDSGibbs.tmix has no ½
--   - encoding: t_mix(ε) ≤ γ_ℓ^{-1} log(n/ε) → for every ε > 0, ≤ ENNReal.ofReal (log(n/ε)/γ_ℓ); reason: the ℝ≥0∞-valued mixing time; ofReal is 0 exactly when ε ≥ n, where t_mix = 0
--   - encoding: stationary state → e^{tL}σ' = σ' for all t ≥ 0; reason: the form used in the proof (p.19)
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Corollary 3.5, (52)–(53), p.19; (20), p.12

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence
import Definitions.Def_QDSGibbs_tmix

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Corollary 3.5 (Summable `η` implies rapid mixing)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Corollary 3.5, (52)–(53), p.19).
Under the assumptions of Theorem 3.4, with `γ_ℓ = 1 − a_η/ℓ`: the Gibbs state `σ_β` is the unique
stationary state of `e^{tL_ℓ}`; `sup_ρ ½‖e^{tL_ℓ}(ρ) − σ_β‖₁ ≤ n e^{−γ_ℓ t}` for every `t ≥ 0`;
and `t_mix(ε) ≤ γ_ℓ^{−1} log(n/ε)`.

**Formalization Note** Stationary means `e^{tL}σ' = σ'` for all `t ≥ 0`. The paper's
`t_mix(ε)` of (20) carries `½‖·‖₁ ≤ ε`; the public `QDSGibbs.tmix` has no `½`, so the paper's
`t_mix(ε)` is `tmix L σ (2ε)`. The bound is stated for every `ε > 0` with `ENNReal.ofReal`, which is
`0` when `ε ≥ n`. -/
theorem corollary_3_5 (n d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (h : Fin n → ChainOp n d)
    (hh : IsPeriodicNN h) (hnorm : ∀ i, opNorm (h i) ≤ 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (η : ℕ → ℝ) (hη : HasExtInfluence β h ℓ η) (hsum : Summable (fun r => η (r + 1)))
    (hlarge : aEta η < ℓ) :
    (∀ σ' : ChainOp n d, IsState σ' →
      ((∀ t : ℝ, 0 ≤ t → sexp (heatBathGen β h ℓ) t σ' = σ') ↔ σ' = gibbs β (∑ i, h i))) ∧
    (∀ ρ : ChainOp n d, IsState ρ → ∀ t : ℝ, 0 ≤ t →
      traceNorm (sexp (heatBathGen β h ℓ) t ρ - gibbs β (∑ i, h i)) / 2 ≤
        n * Real.exp (-((1 - aEta η / ℓ) * t))) ∧
    (∀ ε : ℝ, 0 < ε →
      tmix (heatBathGen β h ℓ) (gibbs β (∑ i, h i)) (2 * ε) ≤
        ENNReal.ofReal (Real.log (n / ε) / (1 - aEta η / ℓ))) := by sorry

end PetzMix
