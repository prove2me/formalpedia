-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_lemma_F_2
-- name    : ProcureAssort.Hotelling.lemma_F_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:38.623344+00:00
-- url     : https://prove2.me/theorems/d0ebb0a4-4f5b-4fa6-9edd-6a26e9d3a9d0
-- title:
--   Lemma F.2, p. 42 — under Theorem 4.1's conditions: an all-active box Θ̃ of discrete intervals (|Θ̃_i| ≥ 3), and paths of profiles from Θ̃
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Let $c^* = \min_{1 \le i \le n-1}(\ell_{i+1} - \ell_i)$ and assume the conditions of Theorem 4.1:
--   (1) some profile $\theta$ has $|v_{i+1}(\theta_{i+1}) - v_i(\theta_i)| \le \delta(\ell_{i+1} - \ell_i)/4$ for $i = 1, \dots, n-1$; (2) $|\Theta_i| \ge 3$ and $v_i(\theta^{j+1}_i) - v_i(\theta^j_i) \le \delta c^*/8$ for consecutive types. Then:
--
--   1. there are sets $\tilde\Theta_i \subseteq \Theta_i$ with $|\tilde\Theta_i| \ge 3$, each a discrete interval of $\Theta_i$ (every $\theta_i \in \Theta_i$ with $\min\tilde\Theta_i \le \theta_i \le \max\tilde\Theta_i$ lies in $\tilde\Theta_i$), such that $Q(\theta) = N$ for every $\theta \in \tilde\Theta = \prod_i \tilde\Theta_i$;
--   2. for every $i$ and every $\theta_i \in \Theta_i$ with $\max\tilde\Theta_i \le \theta_i \le \theta^u_i$ there are a profile $\theta = (\theta_i, \theta_{-i})$ with $i \in Q(\theta)$ and a profile $\theta' \in \tilde\Theta$ joined by a sequence $\theta' = \theta_0, \dots, \theta_K = \theta$ with $Q(\theta_k) \subseteq Q(\theta_{k-1})$ in which the subprofiles of $\theta_{k-1}$ and $\theta_k$ on $Q(\theta_k)$ differ in at most one component.
--
--   Here $\theta^u_i$ is the largest cost at which supplier $i$ can be active.
--
--   **Formalization Note** Property 2 is printed for every profile $\theta = (\theta_i, \theta_{-i})$ with $i \in Q(\theta)$. Its proof (Lemma G.5) builds one path per $\theta_i$, and its only use (Step 1.b) needs one such $\theta$; the existential form is stated. The bounds $\min\tilde\Theta_i$, $\max\tilde\Theta_i$ are given as numbers `lo i`, `hi i` that belong to $\tilde\Theta_i$ and bound it. Condition 1 "for all $i \in N$" is read for $i = 1, \dots, n-1$.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma F.2, p. 42 (proof: electronic companion, Lemma G.5, pp. 52–54)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem lemma_F_2
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (h1 : ∃ θ : Profile Θ, ∀ i : Fin n, ∀ h : i.val + 1 < n,
      |virtualCost Θ f ⟨i.val + 1, h⟩ (θ ⟨i.val + 1, h⟩) - virtualCost Θ f i (θ i)|
        ≤ δ * (ℓ ⟨i.val + 1, h⟩ - ℓ i) / 4)
    (h2 : ∀ i, 3 ≤ (Θ i).card ∧ ∀ a ∈ Θ i, ∀ b ∈ Θ i, a < b → (∀ c ∈ Θ i, ¬ (a < c ∧ c < b)) →
      virtualCost Θ f i b - virtualCost Θ f i a ≤ δ * cstar ℓ hn / 8) :
    ∃ (Θt : Fin n → Finset ℝ) (lo hi : Fin n → ℝ),
      (∀ i, Θt i ⊆ Θ i ∧ 3 ≤ (Θt i).card ∧ lo i ∈ Θt i ∧ hi i ∈ Θt i ∧
        (∀ c ∈ Θt i, lo i ≤ c ∧ c ≤ hi i) ∧ ∀ c ∈ Θ i, lo i ≤ c → c ≤ hi i → c ∈ Θt i) ∧
      (∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ Θt i) → activeSet Θ f ℓ δ θ = Finset.univ) ∧
      (∀ i, ∀ c ∈ Θ i, hi i ≤ c → c ≤ thetaU Θ f ℓ δ i →
        ∃ θ θ' : Profile Θ, (θ i : ℝ) = c ∧ i ∈ activeSet Θ f ℓ δ θ ∧
          (∀ j, (θ' j : ℝ) ∈ Θt j) ∧ Reachable Θ f ℓ δ θ' θ) := by sorry

end ProcureAssort.Hotelling
