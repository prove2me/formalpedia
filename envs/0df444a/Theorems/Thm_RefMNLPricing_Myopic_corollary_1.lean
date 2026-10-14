-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_corollary_1
-- name    : RefMNLPricing.Myopic.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:15.850989+00:00
-- url     : https://prove2.me/theorems/ac93b486-df35-4638-be84-a93c2104b545
-- title:
--   Corollary 1, p. 12 — the right-hand side of (13) is monotone decreasing in Π
-- statement:
--   Let $a_i\in\mathbb R$, $b_i>0$ and $c_i^+,c_i^-\ge0$ for every product $i$, and fix any reference price vector $r$. Let $F(\Pi,r)$ denote the right-hand side of equation (13),
--
--   $$
--   F(\Pi,r) = \sum_{i\in N_l}\lambda_i(\Pi,r_i) + \sum_{i\in N_n}\frac{1}{b_i+c_i}\exp\big(a_i-(b_i+c_i)\Pi + c_i r_i - 1\big) + \sum_{i\in N_g}\gamma_i(\Pi,r_i).
--   $$
--
--   Then $\Pi\mapsto F(\Pi,r)$ is monotone non-increasing on $\mathbb R$: $\Pi\le\Pi'$ implies $F(\Pi',r)\le F(\Pi,r)$.
--
--   Combined with Theorem 1, this is what allows $\Pi^m(r)$ to be computed by one-dimensional bisection.
--
--   **Formalization Note** The paper's "monotone decreasing" is formalized as non-increasing (`Antitone`); strict decrease fails for $n=0$, where $F\equiv0$. The claim is stated for every $r\in\mathbb R^n$, which is the paper's "for a fixed reference price $r$"; it does not use the price box or the ceiling assumption. The algorithmic sentence "Hence, the unique value of $\Pi^m(r)$ can be determined by a one-dimensional bisection method" is not formalized.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 12, Corollary 1

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13

namespace RefMNLPricing.Myopic

/-- Corollary 1, p. 12. For every fixed reference price `r`, the right-hand side of (13) is
monotone non-increasing ("monotone decreasing") in `Π`. -/
theorem corollary_1 {n : ℕ} (a b cp cm : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (r : Fin n → ℝ) :
    Antitone (fun v : ℝ => rhs13 a b cp cm v r) := by sorry

end RefMNLPricing.Myopic
