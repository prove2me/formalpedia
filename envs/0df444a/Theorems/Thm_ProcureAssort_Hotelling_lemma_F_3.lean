-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_lemma_F_3
-- name    : ProcureAssort.Hotelling.lemma_F_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:59.2717+00:00
-- url     : https://prove2.me/theorems/6ef1c36b-01b6-44de-bf10-5ceaa6687d16
-- title:
--   Lemma F.3, p. 43 — if (a, b) satisfies (14), then Σ_{i∈Q(θ)} g_i(θ_i) x_i(θ) = 0 with g_i = b_i / f_i
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Consider coefficients $a^i_\theta$ (one per profile $\theta$ and active supplier $i \in Q(\theta)$, attached to the row $M_i(\theta)$ of the price system) and $b^i_{\theta_i}$ (one per supplier and type, attached to the transfer row $T_i(\theta_i)$). Suppose (14) holds, i.e. the combination $\sum_\theta\sum_{i \in Q(\theta)} a^i_\theta M_i(\theta) + \sum_i\sum_{\theta_i} b^i_{\theta_i} T_i(\theta_i)$ has zero coefficient on every price variable $p_j(\theta)$, $j \in Q(\theta)$:
--   $$\sum_{i \in Q(\theta)} a^i_\theta A_{ij}(\theta) + b^j_{\theta_j}\, f_{-j}(\theta_{-j})\, x^\star_j(\theta) = 0 \qquad \text{for all } \theta,\ j \in Q(\theta).$$
--   Let $g_i(\theta_i) = b^i_{\theta_i}/f_i(\theta_i)$. Then for every $\theta$,
--   $$\sum_{i \in Q(\theta)} g_i(\theta_i)\, x^\star_i(\theta) = 0. \qquad (16)$$
--
--   **Formalization Note** (14) is stated column by column: for each price variable $p_j(\theta)$ the coefficients it receives from the rows $M_i(\theta)$ (entries of $A(\theta)$ of (13)) and from the row $T_j(\theta_j)$ (namely $f_{-j}(\theta_{-j}) x^\star_j(\theta)$) sum, with weights $a$ and $b$, to zero. This is the display with which the page's proof opens.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma F.3, p. 43 (Eq. (14), p. 42)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem lemma_F_3
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (h14 : ∀ θ : Profile Θ, ∀ j ∈ activeSet Θ f ℓ δ θ,
      (∑ i ∈ activeSet Θ f ℓ δ θ, a θ i * pathA (activeSet Θ f ℓ δ θ) i j)
        + b j (θ j) * probOthers f j θ * xstar Θ f ℓ δ θ j = 0) :
    ∀ θ : Profile Θ,
      ∑ i ∈ activeSet Θ f ℓ δ θ, b i (θ i) / f i (θ i) * xstar Θ f ℓ δ θ i = 0 := by sorry

end ProcureAssort.Hotelling
