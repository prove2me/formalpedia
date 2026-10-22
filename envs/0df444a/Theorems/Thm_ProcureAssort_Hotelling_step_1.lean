-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_step_1
-- name    : ProcureAssort.Hotelling.step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:51.665989+00:00
-- url     : https://prove2.me/theorems/7c4714fc-0e23-4da5-8c80-9074cc1a6716
-- title:
--   Proof of Theorem 4.1 (App. F.3), Step 1, pp. 43–45 — under Theorem 4.1's conditions, (14) forces b^i_c = 0 on every transfer row with a nonzero coefficient
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Assume the conditions of Theorem 4.1 (see Lemma F.2) and let the coefficients $(a, b)$ satisfy (14) in the column form of Lemma F.3:
--   $$\sum_{i \in Q(\theta)} a^i_\theta A_{ij}(\theta) + b^j_{\theta_j}\, f_{-j}(\theta_{-j})\, x^\star_j(\theta) = 0 \qquad \text{for all } \theta,\ j \in Q(\theta).$$
--   Then for every supplier $i$ and every type $c \in \Theta_i$ for which some profile $\theta$ with $\theta_i = c$ has $x^\star_i(\theta) > 0$,
--   $$b^i_c = 0, \quad \text{equivalently } g_i(c) = 0.$$
--
--   This is Step 1 of the proof of Theorem 4.1 ("if $(a,b)$ satisfies Eq. (14), all $g_i(\theta_i)$ must be zero"), the combinatorial heart of the argument.
--
--   **Formalization Note** The page concludes $g_i(\theta_i) = 0$ for all $\theta_i \in \Theta_i$. For a type $c$ with $x^\star_i(c, \theta_{-i}) = 0$ for every $\theta_{-i}$ (types above $\theta^u_i$, or types active only at ties with zero demand) the row $T_i(c)$ has an all-zero coefficient vector, so (14) does not constrain $b^i_c$ and the printed claim fails for that row; the paper sets these rows aside (p. 42). The statement covers exactly the rows with a nonzero coefficient, which is what the consistency argument uses.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), proof of Theorem 4.1 (Appendix F.3), Step 1 (Steps 1.a–1.b), pp. 43–45

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem step_1
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
      virtualCost Θ f i b - virtualCost Θ f i a ≤ δ * cstar ℓ hn / 8)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      (∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j)
        + b j (θ j) * probOthers f j θ * xstar Θ f ℓ δ θ j = 0) :
    ∀ i, ∀ c ∈ Θ i, (∃ θ : Profile Θ, (θ i : ℝ) = c ∧ 0 < xstar Θ f ℓ δ θ i) → b i c = 0 := by sorry

end ProcureAssort.Hotelling
