-- Prove2me | Theorems.Thm_PriceDelegation_inventory_identities
-- name    : PriceDelegation.inventory_identities
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:39.369297+00:00
-- url     : https://prove2.me/theorems/b98c0018-bdac-4851-a42d-9e73e9f68f71
-- title:
--   §4.3, p. 25 — $\bar F(\lambda^{f-l})=\rho$ and $\bar F(\varphi^*(\lambda^{n-l}))=\rho$ (corrected: $\lambda^{n-l}$ need not be unique; the second identity needs $\rho\le\bar F(\varphi^*(0))$)
-- statement:
--   Let the valuation satisfy Assumption 2, let $1\le K\le N$ and $\rho=K/N$, and let $\psi$ be any real number.
--
--   1. $f(\lambda)=N\big(E[(V-\lambda)^+]-\psi\big)+K\lambda$ has exactly one minimizer $\lambda^{f-l}$ over $\lambda\ge0$.
--   2. $\bar F(\lambda^{f-l})=\rho$.
--   3. $g(\lambda)=N\max_{\varphi>0}(\varphi-\lambda)\bar F(\varphi)+K\lambda$ has a minimizer over $\lambda\ge0$.
--   4. If $\rho\le\bar F(\varphi^*(0))$, then every minimizer $\lambda^{n-l}\ge0$ of $g$ satisfies
--   $$\bar F(\varphi^*(\lambda^{n-l}))=\rho.$$
--
--   These identities say that the full-learning policy with reservation price $\lambda^{f-l}$, and the no-learning policy with uninformed price $\varphi^*(\lambda^{n-l})$, consume exactly the $K$ units in expectation.
--
--   Differences from the source:
--   - correction: $\lambda^{n-l}$ is uniquely defined (p.25) → a minimizer of $g$ over $\lambda\ge0$ exists, and the identity holds for every one; reason: counterexample: $\bar F(v)=2^{-v}$ on $[0,1]$, $\bar F(v)=\tfrac12e^{-2(v-1)}$ for $v\ge1$ (failure rate $\ln2$ then $2$), $\psi=1/10$, $N=2$, $K=1$: $\varphi^*(\lambda)=1$ and $g(\lambda)/N=1/2$ for all $\lambda\in[0,1/2]$
--   - correction: $\bar F(\varphi^*(\lambda^{n-l}))=\rho$ for every $\rho$ (p.25) → under $\rho\le\bar F(\varphi^*(0))$; reason: counterexample: Exp(1), $\psi=1/10$, $N=K=1$: $g(\lambda)=e^{-1-\lambda}+\lambda$ is minimized at $\lambda^{n-l}=0$ and $\bar F(\varphi^*(0))=1/e\ne1=\rho$; the regime where the paper uses the identity, $\rho\le\bar F(\varphi^*(\lambda^{p-l}))$, implies the added condition
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - generalization: the standing assumptions $\psi>0$ and Assumption 1 of the paper → not assumed; reason: the statement holds without them; the paper's case is the special case where they hold
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), p.25 ("Both λf-l and λn-l are uniquely defined … F̄(λf-l) = ρ and F̄(φ*(λn-l)) = ρ"); proof of Lemma 5, p.ec8

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- The inventory identities (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055
(version of Sept. 22, 2021), p.25, proved in the proof of Lemma 5, p.ec8), with `ρ = K/N`:
1. `N · (E[(V − λ)⁺] − ψ) + K λ` has a unique minimizer `λ^{f-l}` over `λ ≥ 0`;
2. `F̄(λ^{f-l}) = ρ`;
3. `N · max_{φ>0}(φ − λ) F̄(φ) + K λ` has a minimizer over `λ ≥ 0`;
4. if `ρ ≤ F̄(φ*(0))`, then `F̄(φ*(λ^{n-l})) = ρ` for every such minimizer `λ^{n-l}`.

**Corrected**: the page claims `λ^{n-l}` is unique and `F̄(φ*(λ^{n-l})) = ρ` for every `ρ`; the
first fails for a discontinuous hazard rate and the second when the constraint `λ ≥ 0` binds. -/
theorem inventory_identities (V : Valuation) (ψ : ℝ) (hA2 : Assumption2 V) {N K : ℕ}
    (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∃! lf : ℝ, 0 ≤ lf ∧ IsMinOn (Fl V ψ N K) (Ici 0) lf) ∧
      (∀ lf : ℝ, 0 ≤ lf → IsMinOn (Fl V ψ N K) (Ici 0) lf → Fbar V lf = ratio N K) ∧
      (∃ ln : ℝ, 0 ≤ ln ∧ IsMinOn (Gl V N K) (Ici 0) ln) ∧
      (∀ φ0 : ℝ, IsUninf V 0 φ0 → ratio N K ≤ Fbar V φ0 →
        ∀ ln φn : ℝ, 0 ≤ ln → IsMinOn (Gl V N K) (Ici 0) ln → IsUninf V ln φn →
          Fbar V φn = ratio N K) := by sorry

end PriceDelegation
