-- Prove2me | Theorems.Thm_SalesEffort_opt_rate_monotone
-- name    : SalesEffort.opt_rate_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:34.41453+00:00
-- url     : https://prove2.me/theorems/f97c3c2b-b10e-4d46-a375-2fa0ebf37957
-- title:
--   Online Appendix pp.3–4 — the optimal rate is weakly increasing in the marginal value
-- statement:
--   Under Assumption 1, let $\Delta\le\Delta'$, and let $\ell$ and $\ell'$ maximize $\lambda\Delta-c(\lambda)$ and $\lambda\Delta'-c(\lambda)$ over $[\underline\lambda,\bar\lambda]$. Then
--   $$\ell\le\ell'.$$
--
--   Since $\lambda^*(t,n)$ is the maximizer at $\Delta_t(n)$, weak monotonicity of $\Delta_t(n)$ in $t$ or in $n$ transfers to $\lambda^*(t,n)$. This is how the proof of Theorem 1 reduces every statement about $\lambda^*(t,n)$ to one about $\Delta_t(n)$.
--
--   Differences from the source:
--   - encoding: the weak monotonicity in t and n of ∆_t(n) implies the weak monotonicity of λ∗(t,n) → pointwise: ∆ ≤ ∆′ implies ℓ ≤ ℓ′ for the maximizers; reason: composing with t ↦ ∆_t(n) or n ↦ ∆_t(n) gives the printed statement
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Online Appendix pp.3–4 (PDF 37–38), proof of Theorem 1

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **The optimal rate is monotone in the marginal value**, Du, Hu & Wu, SSRN 3506499, Online
Appendix pp.3–4: "λ∗(t,n) = arg max_{λ∈[λ̲,λ̄]} {λ∆t(n) − c(λ)} … Therefore the weak monotonicity
in t and n of ∆t(n) implies the weak monotonicity of λ∗(t,n)."

**Formalization Note.** Stated pointwise and without derivatives of `c`: if `Δ ≤ Δ'` and `ℓ`, `ℓ'`
are maximizers of `λΔ − c(λ)` and `λΔ' − c(λ)` over `[λ̲, λ̄]`, then `ℓ ≤ ℓ'`. Composing with
`t ↦ ∆_t(n)` or `n ↦ ∆_t(n)` gives the printed transfer of weak monotonicity. -/
theorem opt_rate_monotone (M : Model) {Δ Δ' ℓ ℓ' : ℝ} (hΔ : Δ ≤ Δ')
    (hℓ : IsOptRate M Δ ℓ) (hℓ' : IsOptRate M Δ' ℓ') : ℓ ≤ ℓ' := by sorry

end SalesEffort
