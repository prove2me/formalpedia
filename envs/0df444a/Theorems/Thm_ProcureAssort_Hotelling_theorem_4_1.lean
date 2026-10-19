-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_theorem_4_1
-- name    : ProcureAssort.Hotelling.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:40.521185+00:00
-- url     : https://prove2.me/theorems/e9e0a4a6-a3eb-410f-bdb0-24a68bd8cb3f
-- title:
--   Theorem 4.1, p. 24 — general Hotelling model: under Conditions 1–2 on virtual costs, OPT(DecLin) = OPT(Cent)
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Let $c^* = \min_{1 \le i \le n-1}(\ell_{i+1} - \ell_i)$ and suppose that:
--
--   1. there is a profile $\theta \in \Theta$ with $|v_{i+1}(\theta_{i+1}) - v_i(\theta_i)| \le \delta(\ell_{i+1} - \ell_i)/4$ for $i = 1, \dots, n-1$;
--   2. for every $i$, $|\Theta_i| \ge 3$ and $v_i(\theta^{j+1}_i) - v_i(\theta^j_i) \le \delta c^*/8$ for every $1 \le j < |\Theta_i|$.
--
--   Then
--   $$OPT(DecLin) = OPT(Cent),$$
--   where $OPT(Cent)$ is the supremum of $\mathbb E_\theta[GCS(x(\theta)) - \sum_i t_i(\theta)]$ over incentive compatible, individually rational mechanisms with $x(\theta)$ in the simplex, and $OPT(DecLin)$ is the supremum of $\mathbb E_\theta[CS(x(\theta), p(\theta))]$ over mechanisms that post an assortment $q(\theta)$ and unit prices $p(\theta)$, let consumers choose a surplus-maximizing allocation $x(\theta)$ for that menu, and pay each supplier $p_i(\theta) x_i(\theta)$, subject to the same incentive constraints.
--
--   The theorem says that in the Hotelling model with closely spaced virtual costs the auctioneer loses nothing by restricting to linear prices: a framework agreement that posts unit prices and lets consumers choose achieves the centralized optimum.
--
--   **Formalization Note** Both optimal values are real suprema. They are honest: the centralized feasible set is nonempty (equal shares with transfers $(\max\Theta_i)\, x_i$), DecLin's is nonempty (all suppliers offered at a common high price, with the Hotelling demand), and both objectives are at most $0$ ($GCS \le 0$, and (IR) with $x \ge 0$ makes expected transfers nonnegative). Condition 1 "for all $i \in N$" is read for $i = 1, \dots, n-1$. Consecutive types are elements of $\Theta_i$ with no element strictly between them.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem 4.1, p. 24 (proof: Appendix F, pp. 40–45)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem theorem_4_1
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
    optDecLin Θ f (hotGCS ℓ δ) (simplex n) = optCent Θ f (hotGCS ℓ δ) (simplex n) := by sorry

end ProcureAssort.Hotelling
