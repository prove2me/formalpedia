-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_theorem_1
-- name    : SurgeSpatial.Attraction.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:47.143982+00:00
-- url     : https://prove2.me/theorems/210940ec-b799-4793-a628-63a9aaada2da
-- title:
--   Theorem 1, p. 18 — optimal supply and prices within an attraction region
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2) and let $z\in\mathcal C$ be a sink, with attraction region $A(z)=A(z\mid p,\mathcal T)$ and ray endpoints $X_a=X_a(z\mid p,\mathcal T)$, $a\in R_z$. Then there exist another feasible solution $(\hat p,\hat{\mathcal T})$ of (P2) with at least the same (P2) value,
--   $$\gamma\int_{\mathcal C}V(x\mid p,\mathcal T)\,s^{\mathcal T}(x)\,d\Gamma(x)\ \le\ \gamma\int_{\mathcal C}V(x\mid\hat p,\hat{\mathcal T})\,s^{\hat{\mathcal T}}(x)\,d\Gamma(x),$$
--   points $r_a\in[z,X_a]$ and numbers $s_a\ge0$, $a\in R_z$, such that on $A(z)$ the new supply is
--   $$s^{\hat{\mathcal T}}(x)=\begin{cases}\psi_x^{-1}\big(V(z\mid p,\mathcal T)-\|x-z\|\big)& x\in\bigcup_{a}[z,r_a),\\ s_a & x=r_a,\\ 0&\text{otherwise},\end{cases}$$
--   and the new prices are
--   $$\hat p(x)=\begin{cases}\rho^{loc}_x\big(s^{\hat{\mathcal T}}(x)\big)&x\in A(z)\setminus\bigcup_a\{r_a\},\\ p_a & x=r_a,\end{cases}$$
--   where $p_a$ satisfies $U(r_a,p_a,s_a)=V(r_a\mid p,\mathcal T)$.
--
--   Within an attraction region, it is never worse to fill each ray outward from the sink up to the congestion bound and price each location as a local monopolist; this is the paper's local characterization of optimal prices and supply.
--
--   **Formalization Note** All case formulas hold for $\Gamma$-a.e. $x\in A(z)$, since densities are defined only up to null sets (at an atom of $\Gamma$ this is pointwise). The first case is stated as $\psi_x(s^{\hat{\mathcal T}}(x))=V(z\mid p,\mathcal T)-\|x-z\|$, which is $s^{\hat{\mathcal T}}(x)=\psi_x^{-1}(\cdot)$ by Lemma A-3. The cases are read in the printed order: the second case applies at $r_a$ only when it is not covered by some $[z,r_b)$ (relevant at $z$), and "otherwise" is $A(z)\setminus\bigcup_a[z,r_a]$. $p_a$ is $\hat p(r_a)$. $V(z\mid p,\mathcal T)$ and $V(r_a\mid p,\mathcal T)$ refer to the old pair.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. 18, Theorem 1

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem theorem_1 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z) :
    ∃ (pHat : E → ℝ) (THat : Measure (E × E)) (r : S1 → E) (s : S1 → ℝ),
      M.FeasibleP2 pHat THat ∧ M.objP2 p T ≤ M.objP2 pHat THat ∧
      (∀ a, r a ∈ segment ℝ z (M.Xend p T z a) ∧ 0 ≤ s a) ∧
      ∀ᵐ x ∂M.Γ, x ∈ M.attr p T z →
        (x ∈ ⋃ a, (segment ℝ z (r a) \ {r a}) →
            M.psi x (M.sT THat x) = M.V p T z - ‖x - z‖) ∧
        (∀ a, x = r a → x ∉ ⋃ b, (segment ℝ z (r b) \ {r b}) → M.sT THat x = s a) ∧
        (x ∉ ⋃ a, segment ℝ z (r a) → M.sT THat x = 0) ∧
        ((∀ a, x ≠ r a) → pHat x = M.rhoLoc x (M.sT THat x)) ∧
        (∀ a, x = r a → M.Ufun x (pHat x) (s a) = M.V p T x) := by sorry

end SurgeSpatial.Attraction
