-- Prove2me | Theorems.Thm_PetzMix_corollary_5_6
-- name    : PetzMix.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:38.044199+00:00
-- url     : https://prove2.me/theorems/d60a77e2-ba93-4f35-addf-c78ca41b1956
-- title:
--   Corollary 5.6 — two-interval Gibbs factorization
-- statement:
--   Fix $d$ and $\beta\ge0$. There are constants $C_{\mathrm{fac}},\mu_{\mathrm{fac}}>0$ such that for every Hamiltonian $H$ in the family (1), every block $I$, and every decomposition $I=XGY$ into three consecutive intervals,
--   $$
--   \|(\tau_I)_{XY}-(\tau_I)_X\otimes(\tau_I)_Y\|_1\le C_{\mathrm{fac}}e^{-\mu_{\mathrm{fac}}|G|},
--   $$
--   where $\tau_I$ is the Gibbs state of $H_I$ (the interactions inside $I$) and $(\tau_I)_S$ its marginal on $S$.
--
--   It is the input from which Assumption 4.4 follows (Theorem 5.7).
--
--   **Formalization Note** $X,G,Y$ are the offsets $[0,p)$, $[p,q)$, $[q,\ell)$ along $I$ from its left end; marginals are the public normalized full-space `marg`/`margProd` of `gibbs β (HB h I)`.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: an interval I → a block cycBlock ℓ a with 1 ≤ ℓ < n of the periodic chain; reason: the intervals to which the corollary is applied (Theorem 5.7) are the blocks
--   - encoding: constants depending only on β and d, independent of n → ∃ constants after (d, β), before n, h and the block; reason: the meaning of 'depending only on β and d'
--   - generalization: three consecutive intervals X, G, Y → X, G, Y possibly empty; reason: empty X or Y gives 0 on the left; empty G is the bound with |G| = 0; nonempty parts are included
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Corollary 5.6, (113), p.31

import Mathlib
import Definitions.Def_PetzMix_petzAmp
import Definitions.Def_QDSGibbs_cov

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Corollary 5.6 (Two-interval Gibbs factorization)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Corollary 5.6, (113), p.31). Fix `d`
and `β`. There exist constants `C_fac, µ_fac > 0`, depending only on `β` and `d`, such that for every
Hamiltonian of the family (1) and every interval `I = XGY` decomposed into three consecutive
intervals, `‖(τ_I)_{XY} − (τ_I)_X ⊗ (τ_I)_Y‖₁ ≤ C_fac e^{−µ_fac |G|}`.

**Formalization Note** `I = cycBlock ℓ a`, `1 ≤ ℓ < n`, and `τ_I` is the Gibbs state of `H_I` (the
interactions inside `I`, (101)/(103)); its normalized full-space form is `gibbs β (HB h I)`.
`X = [0, p)`, `G = [p, q)`, `Y = [q, ℓ)` along `I` from `a`; every part may be empty. Marginals are
the public `marg`, `margProd`. -/
theorem corollary_5_6 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Cfac μfac : ℝ, 0 < Cfac ∧ 0 < μfac ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n → ∀ p q : ℕ, p ≤ q → q ≤ ℓ →
        traceNorm (marg (seg a 0 p ∪ seg a q ℓ) (gibbs β (HB h (cycBlock ℓ a))) -
            margProd (seg a 0 p) (seg a q ℓ) (gibbs β (HB h (cycBlock ℓ a)))) ≤
          Cfac * Real.exp (-(μfac * ((q - p : ℕ) : ℝ))) := by sorry

end PetzMix
