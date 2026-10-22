-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_eq_M_implies_demand
-- name    : ProcureAssort.Hotelling.eq_M_implies_demand
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:41.979684+00:00
-- url     : https://prove2.me/theorems/4f33cf9d-501c-41d6-a709-aeabeea2eb30
-- title:
--   App. F.1, pp. 40–41, (M_i(θ)) and (13) — prices with A(θ)p = A(θ)v(θ) on Q(θ) decentralize x⋆(θ), i.e. satisfy (10)
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Fix a profile $\theta$ and a price vector $p$ that solves the system $(M_i(\theta))$, i.e. in matrix form $A(\theta)\, p = A(\theta)\, v(\theta)$ on the active set $Q(\theta)$:
--   $$p_{(2)} - p_{(1)} = v_{(2)} - v_{(1)}, \quad p_{(i-1)} - 2p_{(i)} + p_{(i+1)} = v_{(i-1)} - 2v_{(i)} + v_{(i+1)}, \quad p_{(k-1)} - p_{(k)} = v_{(k-1)} - v_{(k)},$$
--   where $(1), \dots, (k)$ are the active suppliers in location order and $v_{(i)} = v_{(i)}(\theta_{(i)})$. Then $x^\star(\theta)$ is a consumer-optimal demand for the assortment $\{i : x^\star_i(\theta) > 0\}$ at prices $p$; that is, $p$ satisfies (10) for the centralized-optimal allocation.
--
--   **Formalization Note** The page presents $(M_i(\theta))$ as the form (10) takes in the Hotelling model; only the direction used in the proof (solutions of $(M_i(\theta))$ satisfy (10)) is stated. With one active supplier $A(\theta) = 0$ and the system is empty.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Appendix F.1, pp. 40–41, system (M_i(θ)) and matrix (13)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem eq_M_implies_demand
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (θ : Profile Θ) (p : Fin n → ℝ)
    (hM : ∀ i ∈ activeSet Θ f ℓ δ θ,
      ∑ j ∈ activeSet Θ f ℓ δ θ, pathA (activeSet Θ f ℓ δ θ) i j * p j =
        ∑ j ∈ activeSet Θ f ℓ δ θ, pathA (activeSet Θ f ℓ δ θ) i j * vvec Θ f θ j) :
    IsDemand (hotGCS ℓ δ) (simplex n) (Finset.univ.filter (fun i => 0 < xstar Θ f ℓ δ θ i)) p
      (xstar Θ f ℓ δ θ) := by sorry

end ProcureAssort.Hotelling
