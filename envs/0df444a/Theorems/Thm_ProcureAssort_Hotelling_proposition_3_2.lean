-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_proposition_3_2
-- name    : ProcureAssort.Hotelling.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:39.26999+00:00
-- url     : https://prove2.me/theorems/3937c5c1-e3e1-4c8a-991e-6c9fa9e54819
-- title:
--   Proposition 3.2 (parts 1–2), p. 14 — for the general Hotelling model, (x⋆, t⋆) is feasible, meets Proposition 3.1's conditions, t⋆ ≥ θx⋆, t⋆ = 0 when x⋆ = 0
-- statement:
--   **Standing assumptions (general Hotelling model, §2, §3.1, §3.2.1).** There are $n \ge 2$ suppliers $i = 1, \dots, n$ located at $0 \le \ell_1 < \dots < \ell_n \le 1$; consumers of total mass $1$ are uniform on $[0,1]$ and the transportation cost is $\delta > 0$. Supplier $i$'s private cost $\theta_i$ lies in a finite set $\Theta_i$ of strictly positive reals, with probability mass function $f_i > 0$ on $\Theta_i$ summing to $1$, independently across suppliers. The virtual costs $v_i(\theta_i) = \theta_i + \frac{F_i(\rho_i(\theta_i))}{f_i(\theta_i)}(\theta_i - \rho_i(\theta_i))$ (Definition 3.1) are strictly increasing on $\Theta_i$ (Assumption 3.1). The consumption set is the simplex $\mathcal X = \{x \ge 0 : \sum_i x_i = 1\}$, and $GCS$ is minus $\delta$ times the total transportation cost. $Q(\theta) = \{i : v_i(\theta_i) - v_j(\theta_j) \le \delta|\ell_j - \ell_i| \ \forall j\}$ is the centralized-optimal assortment and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$.
--
--   Let $x^\star(\theta)$ be the Hotelling demand at prices $v(\theta)$ and, for $\theta_i = \theta^j_i$,
--   $$t^\star_i(\theta^j_i, \theta_{-i}) = \theta^j_i x^\star_i(\theta^j_i, \theta_{-i}) + \sum_{k = j+1}^{|\Theta_i|}(\theta^k_i - \theta^{k-1}_i)\, x^\star_i(\theta^k_i, \theta_{-i})$$
--   (Appendix B). Then:
--
--   1. $(x^\star, t^\star)$ is feasible for Cent;
--   2. it satisfies the three conditions of Proposition 3.1: $x^\star(\theta) \in \operatorname{argmax}_{x \in \mathcal X} CS(x, v(\theta))$, $X^\star_i$ is decreasing, and $T^\star_i$ satisfies (7);
--   3. for all $i$ and $\theta$, $t^\star_i(\theta) \ge \theta_i x^\star_i(\theta)$, and $t^\star_i(\theta) = 0$ whenever $x^\star_i(\theta) = 0$.
--
--   This exhibits an optimal centralized mechanism with ex-post individually rational transfers, the starting point of the decentralization analysis.
--
--   **Formalization Note** The page states Proposition 3.2 for the Hotelling model of Example 2.1 (two suppliers) and the affine model; the proof of Theorem 4.1 uses it for the general Hotelling model (p. 40), which is the case stated here, with the solution constructed explicitly. The uniqueness clause ("x and T are unique") is not stated: with interior locations the demand is not unique at ties.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed (Lean's `i` is the paper's supplier $i+1$). $n \ge 2$ is assumed throughout (the constant $c^*$ of Theorem 4.1 needs two suppliers), and $f_i > 0$ on $\Theta_i$ (the virtual cost divides by $f_i(\theta_i)$). Profiles are dependent functions `(i : Fin n) → Θ i`. All objects are those of the definition item `ProcureAssort.Hotelling.Setting`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Proposition 3.2, p. 14 (proof: Appendix B, pp. 37–38; general Hotelling model as used on p. 40)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem proposition_3_2
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    IsCentFeasible f (simplex n) (xstar Θ f ℓ δ) (tstar Θ (xstar Θ f ℓ δ)) ∧
    (∀ θ, xstar Θ f ℓ δ θ ∈ simplex n ∧ ∀ y ∈ simplex n,
      CS (hotGCS ℓ δ) y (vvec Θ f θ) ≤ CS (hotGCS ℓ δ) (xstar Θ f ℓ δ θ) (vvec Θ f θ)) ∧
    (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b → interim f (fun θ => xstar Θ f ℓ δ θ i) i b ≤ interim f (fun θ => xstar Θ f ℓ δ θ i) i a) ∧
    (∀ i, ∀ c ∈ Θ i, interim f (fun θ => tstar Θ (xstar Θ f ℓ δ) θ i) i c =
      c * interim f (fun θ => xstar Θ f ℓ δ θ i) i c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => xstar Θ f ℓ δ θ i) i b) ∧
    (∀ (θ : Profile Θ) (i : Fin n),
      (θ i : ℝ) * xstar Θ f ℓ δ θ i ≤ tstar Θ (xstar Θ f ℓ δ) θ i ∧
      (xstar Θ f ℓ δ θ i = 0 → tstar Θ (xstar Θ f ℓ δ) θ i = 0)) := by sorry

end ProcureAssort.Hotelling
