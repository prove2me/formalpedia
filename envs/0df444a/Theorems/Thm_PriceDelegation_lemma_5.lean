-- Prove2me | Theorems.Thm_PriceDelegation_lemma_5
-- name    : PriceDelegation.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:34.671474+00:00
-- url     : https://prove2.me/theorems/a923a4c1-f2ef-453a-9874-65acfa53f6a2
-- title:
--   Lemma 5 — the optimal multiplier of the dual (8) in each regime (corrected: $\lambda^{n-l}$ is any minimizer of $g$; uniqueness only where it holds)
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, let $1\le K\le N$ and $\rho=K/N$. Let $\lambda^{p-l}\ge0$ be the zero of $\Delta$ (Lemma 4) and $\varphi^{p-l}=\varphi^*(\lambda^{p-l})$. Consider the dual problem (8), $\min_{\lambda\ge0}J_\lambda$, with $J_\lambda$ as in (9), and write $f(\lambda)=N(E[(V-\lambda)^+]-\psi)+K\lambda$ and $g(\lambda)=N\max_{\varphi>0}(\varphi-\lambda)\bar F(\varphi)+K\lambda$.
--
--   1. If $\rho\ge\bar F(\lambda^{p-l})$, the minimizer $\lambda^{f-l}$ of $f$ over $\lambda\ge0$ is the unique minimizer of $J_\lambda$ over $\lambda\ge0$.
--   2. If $\bar F(\varphi^{p-l})\le\rho\le\bar F(\lambda^{p-l})$, then $\lambda^{p-l}$ minimizes $J_\lambda$ over $\lambda\ge0$, and it is the unique minimizer when $\bar F(\varphi^{p-l})<\rho$.
--   3. If $\rho\le\bar F(\varphi^{p-l})$, every minimizer of $J_\lambda$ over $\lambda\ge0$ minimizes $g$ over $\lambda\ge0$; every minimizer $\lambda\ge\lambda^{p-l}$ of $g$ minimizes $J_\lambda$; and such a minimizer exists.
--
--   In each regime the lemma names the shadow price of inventory that the first-best policy and the contract of Lemma 7 use as a reservation price.
--
--   Differences from the source:
--   - correction: $\lambda^*=\lambda^{n-l}$, the unique minimizer of $g$, if $\rho\le\bar F(\varphi^*(\lambda^{p-l}))$ → every minimizer of $J$ minimizes $g$, and the minimizers of $g$ in $[\lambda^{p-l},\infty)$ minimize $J$; reason: $g$ can have a whole interval of minimizers (counterexample in inventory_identities), so "the" $\lambda^{n-l}$ need not exist
--   - correction: $\lambda^*$, "the optimal solution to (8)", is $\lambda^{p-l}$ when $\bar F(\varphi^*(\lambda^{p-l}))\le\rho\le\bar F(\lambda^{p-l})$ → $\lambda^{p-l}$ is a minimizer, and the unique one when $\bar F(\varphi^*(\lambda^{p-l}))<\rho$; reason: at $\rho=\bar F(\varphi^*(\lambda^{p-l}))$, $J=g$ on $[\lambda^{p-l},\infty)$, which is flat where $\varphi^*$ is constant (same counterexample)
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Lemma 5, p.26; proof, pp.ec7–ec8

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Lemma 5 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), p.26): the optimal multiplier of the dual problem (8), `min_{λ≥0} J_λ`, in each
regime of `ρ = K/N`. Let `λ^{p-l} ≥ 0` be the zero of `∆` (Lemma 4) and `φ^{p-l} = φ*(λ^{p-l})`.
1. If `ρ ≥ F̄(λ^{p-l})`: the minimizer `λ^{f-l}` of `N(E[(V − λ)⁺] − ψ) + Kλ` over `λ ≥ 0` is the
   unique minimizer of `J_λ` over `λ ≥ 0`.
2. If `F̄(φ^{p-l}) ≤ ρ ≤ F̄(λ^{p-l})`: `λ^{p-l}` minimizes `J_λ` over `λ ≥ 0`, uniquely when
   `F̄(φ^{p-l}) < ρ`.
3. If `ρ ≤ F̄(φ^{p-l})`: every minimizer of `J_λ` over `λ ≥ 0` minimizes
   `g(λ) = N max_{φ>0}(φ − λ)F̄(φ) + Kλ` over `λ ≥ 0` (it is a `λ^{n-l}`); every minimizer of `g`
   with `λ ≥ λ^{p-l}` minimizes `J_λ`; and such a minimizer exists.

**Corrected**: the page names a unique `λ^{n-l}`, which need not exist (see
`inventory_identities`). -/
theorem lemma_5 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V)
    {lp φp : ℝ} (hlp : 0 ≤ lp) (hΔ : Delta V ψ N lp = 0) (hφp : IsUninf V lp φp) :
    (Fbar V lp ≤ ratio N K → ∀ lf : ℝ, 0 ≤ lf → IsMinOn (Fl V ψ N K) (Ici 0) lf →
        IsMinOn (Jdual V ψ N K) (Ici 0) lf ∧
          ∀ lam : ℝ, 0 ≤ lam → IsMinOn (Jdual V ψ N K) (Ici 0) lam → lam = lf) ∧
      (Fbar V φp ≤ ratio N K → ratio N K ≤ Fbar V lp →
        IsMinOn (Jdual V ψ N K) (Ici 0) lp ∧
          (Fbar V φp < ratio N K → ∀ lam : ℝ, 0 ≤ lam →
            IsMinOn (Jdual V ψ N K) (Ici 0) lam → lam = lp)) ∧
      (ratio N K ≤ Fbar V φp →
        (∀ lam : ℝ, 0 ≤ lam → IsMinOn (Jdual V ψ N K) (Ici 0) lam →
            IsMinOn (Gl V N K) (Ici 0) lam) ∧
          (∀ lam : ℝ, lp ≤ lam → IsMinOn (Gl V N K) (Ici 0) lam →
            IsMinOn (Jdual V ψ N K) (Ici 0) lam) ∧
          ∃ lam : ℝ, lp ≤ lam ∧ IsMinOn (Gl V N K) (Ici 0) lam) := by sorry

end PriceDelegation
