-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_proposition_3_1
-- name    : ProcureAssort.Hotelling.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:42.480029+00:00
-- url     : https://prove2.me/theorems/dd49a843-203d-408d-8bac-29aeda752a8d
-- title:
--   Proposition 3.1, pp. 13–14 — virtual-cost demand, monotone interim allocations and transfers (7) give an optimal centralized mechanism
-- statement:
--   Let suppliers $i \in N$ have finite type sets $\Theta_i$ of strictly positive costs with pmfs $f_i > 0$, and strictly increasing virtual costs $v_i$ (Assumption 3.1). Let $GCS$ be any gross consumer surplus and $\mathcal X$ any set of nonnegative consumption vectors. Suppose an allocation $x$ and transfers $t$ satisfy:
--
--   1. for every profile $\theta$, $x(\theta) \in \mathcal X$ and $x(\theta) \in \operatorname{argmax}_{x' \in \mathcal X} CS(x', v(\theta))$;
--   2. interim allocations are decreasing: $X_i(\theta) \ge X_i(\theta')$ for all $\theta \le \theta'$ in $\Theta_i$;
--   3. interim transfers satisfy, for all $i$ and $\theta^j_i \in \Theta_i$,
--   $$T_i(\theta^j_i) = \theta^j_i X_i(\theta^j_i) + \sum_{k = j+1}^{|\Theta_i|} (\theta^k_i - \theta^{k-1}_i) X_i(\theta^k_i).$$
--
--   Then $(x, t)$ is feasible for the centralized problem Cent, and its objective $\mathbb E_\theta[GCS(x(\theta)) - \sum_i t_i(\theta)]$ is at least that of every feasible $(x', t')$.
--
--   This is the discrete-type Myerson characterization of the centralized optimum: the auctioneer maximizes consumer surplus with prices replaced by virtual costs.
--
--   **Formalization Note** The page states the result for general demand models; $GCS$ and $\mathcal X$ are arbitrary here, except that consumption vectors are nonnegative ($\mathcal X \subseteq \mathbb R^n_{\ge 0}$, p. 8, and the row $0 \le X_i(\theta^{m_i})$ of the proof in Appendix A); without it (IR) can fail. Compactness and convexity of $\mathcal X$ are not needed and not assumed. "Optimal mechanism" is stated as feasibility plus optimality among feasible pairs. The sum in (7) runs over the elements of $\Theta_i$ above $\theta^j_i$, each weighted by the gap to its predecessor.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Proposition 3.1, pp. 13–14 (proof: Appendix A, pp. 36–37)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem proposition_3_1
    {n : ℕ} (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ))
    (hX : ∀ y ∈ X, ∀ i, 0 ≤ y i)
    (x t : Profile Θ → Fin n → ℝ)
    (hcond1 : ∀ θ, x θ ∈ X ∧ ∀ y ∈ X, CS GCS y (vvec Θ f θ) ≤ CS GCS (x θ) (vvec Θ f θ))
    (hcond2 : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b →
      interim f (fun θ => x θ i) i b ≤ interim f (fun θ => x θ i) i a)
    (hcond3 : ∀ i, ∀ c ∈ Θ i, interim f (fun θ => t θ i) i c =
      c * interim f (fun θ => x θ i) i c +
        ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => x θ i) i b) :
    IsCentFeasible f X x t ∧
      ∀ x' t' : Profile Θ → Fin n → ℝ, IsCentFeasible f X x' t' →
        centObj f GCS x' t' ≤ centObj f GCS x t := by sorry

end ProcureAssort.Hotelling
