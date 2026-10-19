-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_step_2
-- name    : ProcureAssort.Hotelling.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:40.561989+00:00
-- url     : https://prove2.me/theorems/edb5e31e-3a5d-4b2c-a67a-4a2ba7c6c0a3
-- title:
--   Proof of Theorem 4.1 (App. F.3), Step 2, p. 45 — (a, 0) satisfying (14) also satisfies (15)
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Let coefficients $a^i_\theta$ ($i \in Q(\theta)$) satisfy (14) with $b = 0$, i.e. $\sum_{i \in Q(\theta)} a^i_\theta A_{ij}(\theta) = 0$ for every $\theta$ and $j \in Q(\theta)$. Then (15) holds with $b = 0$:
--   $$\sum_{\theta \in \Theta} \sum_{i \in Q(\theta)} a^i_\theta \Big(\sum_{j \in Q(\theta)} A_{ij}(\theta)\, v_j(\theta_j)\Big) = 0.$$
--
--   This is the final step of the consistency argument: once all transfer-row coefficients vanish, the right-hand side combination vanishes too.
--
--   **Formalization Note** $A(\theta)$ is the matrix (13) on the active set $Q(\theta)$, as in the definition item.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), proof of Theorem 4.1 (Appendix F.3), Step 2, p. 45 (Eq. (15), p. 42)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem step_2
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (a : Profile Θ → Fin n → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      ∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j = 0) :
    ∑ θ : Profile Θ, ∑ i ∈ activeSet Θ f ℓ δ θ,
      a θ i * ∑ j ∈ activeSet Θ f ℓ δ θ, pathA (activeSet Θ f ℓ δ θ) i j * vvec Θ f θ j = 0 := by sorry

end ProcureAssort.Hotelling
