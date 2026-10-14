-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_theorem_3
-- name    : UnknownLoads.Coxian.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:54.007104+00:00
-- url     : https://prove2.me/theorems/dcd2f5c2-e928-42d6-9d60-828d7f28be26
-- title:
--   Theorem 3 — under Coxian service and the basic learning scheme, the threshold settles at ⌊ρ⌋_Δ and the load becomes nearly balanced
-- statement:
--   Consider $n$ server pools fed by Poisson arrivals of constant rate $n\lambda$, with Coxian service times with $r$ phases, offered load $\rho = \lambda/\mu$ per pool, the threshold dispatching rule with parameter $\Delta \ge 1$, and the basic learning scheme $\ell_n(t) = \lfloor u_n(t)\rfloor_\Delta$, where $u_n$ is the total number of tasks divided by $n$. All systems are built on one probability space by the coupled construction of Section 6.1.1, and $q_n(t,i)$ is the fraction of pools with at least $i$ tasks at time $t$.
--
--   Suppose that $\rho \notin \{i\Delta : i \in \mathbb N\}$ (with $0\in\mathbb N$). Then there exist constants $\sigma, \eta, c > 0$, which do not depend on the horizon $T$, such that for every $T$ the following three statements hold with probability one:
--   $$\lim_{n\to\infty}\ \sup_{t\in[\sigma,T]} \big|\ell_n(t) - \lfloor\rho\rfloor_\Delta\big| = 0, \tag{8a}$$
--   $$\lim_{n\to\infty}\ \sup_{t\in[\sigma,T]} \big|1 - q_n(t,i)\big| = 0 \qquad \text{for all } i \le \lfloor\rho\rfloor_\Delta, \tag{8b}$$
--   $$\limsup_{n\to\infty}\ \sup_{t\in[\sigma,T]}\ \sum_{i > \lfloor\rho\rfloor_\Delta + \Delta} q_n(t,i)\, e^{\eta(t-\sigma)} \le c. \tag{8c}$$
--
--   Thus, after time $\sigma$, the threshold of every large system equals $\lfloor\rho\rfloor_\Delta$, almost all pools have at least $\lfloor\rho\rfloor_\Delta$ tasks, and the mass beyond $\lfloor\rho\rfloor_\Delta+\Delta$ tasks decays exponentially at rate $\eta$. The hypothesis on $\rho$ excludes the case in which the threshold can oscillate between $\rho-\Delta$ and $\rho$.
--
--   **Formalization Note** The constants are quantified before the horizon $T$ ("The constants σ, η and c do not depend on T"), and the system is horizon-free (its equations hold for all $t \ge 0$); with $T$ fixed first, (8c) would be trivial. (8a) and (8b) are uniform convergence on $[\sigma,T]$. In (8c) the tail sum and the supremum are taken in $[0,\infty]$, so the bound cannot hold through a non-summable family. The coupled construction is the `System` structure (see the `Construction` definition).
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 20, Theorem 3

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Construction
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Theorem 3 (p. 20). If `ρ ∉ {iΔ : i ∈ ℕ}`, there are constants `σ, η, c > 0`, not depending
on `T`, such that for every horizon `T`, almost surely, (8a) `ℓ_n → ⌊ρ⌋_Δ` uniformly on
`[σ, T]`, (8b) `q_n(i) → 1` uniformly on `[σ, T]` for all `i ≤ ⌊ρ⌋_Δ`, and (8c)
`limsup_n sup_{t ∈ [σ,T]} Σ_{i > ⌊ρ⌋_Δ + Δ} q_n(t, i) e^{η(t-σ)} ≤ c` (sums in `ℝ≥0∞`). -/
theorem theorem_3 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (hρ : ∀ i : ℕ, rho P ≠ (i : ℝ) * (P.Δ : ℝ)) :
    ∃ σ η c : ℝ, 0 < σ ∧ 0 < η ∧ 0 < c ∧ ∀ T : ℝ, ∀ᵐ ω ∂μP,
      TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => (sys.ℓ n ω t : ℝ))
          (fun _ => ((floorDelta P.Δ (rho P) : ℤ) : ℝ)) atTop (Set.Icc σ T) ∧
      (∀ i : ℕ, (i : ℤ) ≤ floorDelta P.Δ (rho P) →
          TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => sys.q n ω t i) (fun _ => (1 : ℝ)) atTop
            (Set.Icc σ T)) ∧
      Filter.limsup (fun n : ℕ => ⨆ t ∈ Set.Icc σ T,
          (∑' i : ℕ, if floorDelta P.Δ (rho P) + (P.Δ : ℤ) < (i : ℤ)
              then ENNReal.ofReal (sys.q n ω t i) else 0) *
            ENNReal.ofReal (Real.exp (η * (t - σ)))) atTop ≤ ENNReal.ofReal c := by sorry

end UnknownLoads.Coxian
