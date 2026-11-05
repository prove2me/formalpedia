-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_sdp_lower_bound_of_certificate
-- name    : QuantumMaxCutEnergy.sdp_lower_bound_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:14:38.307102+00:00
-- url     : https://prove2.me/theorems/912837e3-50dd-44bb-a0cb-1cfd7123266f
-- title:
--   A primal-dual certificate pins the Max-Cut SDP value to relative accuracy $10^{-4}$
-- statement:
--   **From a primal-dual certificate to a two-sided bound on the Max-Cut SDP value.**
--
--   Let $G$ be a weighted graph with weight matrix $A=A(G)$ and total weight $W=\sum_e w_e$, and let $S$ be the optimal value of the Max-Cut semidefinite relaxation $\max\{\tfrac14\sum_{i,j}A_{ij}(1-X_{ij}) : X\succeq0,\ X_{ii}=1\}$. Suppose we are given
--   * a matrix $X\succeq0$ with $X_{ii}=1$ (primal feasibility),
--   * a vector $\lambda$ with $A+\operatorname{diag}\lambda\succeq0$ (dual feasibility),
--   * a nonnegative rational $L$ with $L\le\tfrac14\sum_{i,j}A_{ij}(1-X_{ij})$ (the value we report),
--   * and the gap condition $\tfrac14\big(\sum_{i,j}A_{ij}+\sum_i\lambda_i\big)-L\le W/10^4$.
--
--   Then
--   $$L\;\le\; S\;\le\; L+\frac{W}{10^4}.$$
--
--   The proof is the two halves of weak duality: primal feasibility gives $\tfrac14\sum_{i,j}A_{ij}(1-X_{ij})\le S$, so $L\le S$; and dual feasibility gives $S\le\tfrac14(\sum_{i,j}A_{ij}+\sum_i\lambda_i)\le L+W/10^4$. No strong duality, no attainment, and no eigenvalue computation is used — the two inequalities are elementary and the certificate is finite rational data.
--
--   This is exactly the second conjunct of `QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`, with the *existence* of the certificate pair factored out. What remains for that node is the algorithmic content: producing, for every graph and in time polynomial in the encoding length, a rational pair $(X,\lambda,L)$ meeting the gap condition.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; weak duality for the MAXCUT SDP, in the certificate form used by numerical solvers. Interface for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix

open Matrix
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **A certificate pair bounds the Max-Cut SDP value.** If `X` is feasible, `lam` is dual
feasible for the weight matrix of `G`, `L` is at most the objective at `X`, and the duality gap
`(1/4)(Σ_{i,j} a_ij + Σ_i lam i) - L` is at most `1/10000` of the total edge weight, then the
optimal value `S` of the relaxation satisfies `L ≤ S ≤ L + W/10000`. -/
theorem sdp_lower_bound_of_certificate (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (lam : Fin G.n → ℝ) (L : ℚ≥0)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X)
    (hdual : (weightMatrix G + Matrix.diagonal lam).PosSemidef)
    (hLle : (L : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G) X)
    (hgap : (1 / 4) * ((∑ i, ∑ j, weightMatrix G i j) + ∑ i, lam i) - (L : ℝ)
        ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    ∀ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S →
      (L : ℝ) ≤ S ∧ S - (L : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry

end QuantumMaxCutEnergy
