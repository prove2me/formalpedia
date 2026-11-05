-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_certificate_program
-- name    : QuantumMaxCutEnergy.agm_sdp_certificate_program
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:55:41.974121+00:00
-- url     : https://prove2.me/theorems/0583956e-294e-499a-9b99-12694eb3ff3b
-- title:
--   Polynomial-time rational value with a primal-dual certificate of gap $10^{-4}W$
-- statement:
--   **The algorithmic core of the Max-Cut SDP lower value, with its certificate.**
--
--   There is a polynomial-time computable map $G\mapsto L(G)\in\mathbb Q_{\ge0}$ together with, for every weighted graph $G$ on $n$ vertices, a real $S$ and data $(X,\lambda)$ such that
--   1. $S$ is the optimal value of the Max-Cut semidefinite relaxation of the weight matrix $A(G)$;
--   2. $X\succeq0$ with $X_{ii}=1$ is feasible, and $\lambda$ is dual feasible, $A(G)+\operatorname{diag}\lambda\succeq0$;
--   3. $L(G)\le\tfrac14\sum_{i,j}A(G)_{ij}(1-X_{ij})$, i.e. the reported value does not exceed the objective at a feasible point;
--   4. $\tfrac14\big(\sum_{i,j}A(G)_{ij}+\sum_i\lambda_i\big)-L(G)\le W/10^4$, where $W=\sum_e w_e$ is the total weight.
--
--   The pair $(X,\lambda)$ is what makes the statement an *algorithmic* claim rather than a numerical coincidence: exhibiting a primal-dual pair whose duality gap is at most $10^{-4}$ of the total weight is equivalent to solving the relaxation to that accuracy. Once such a pair is available, the two halves of weak duality turn it into the two-sided bound $L(G)\le S\le L(G)+W/10^4$ — that step is the already-proved `QuantumMaxCutEnergy.sdp_lower_bound_of_certificate`.
--
--   The intended construction is an ellipsoid method on the primal body $\{X\succeq0,\ X_{ii}=1\}$ in exact rational arithmetic: the body is compact and convex, the PSD separation oracle and the affine subgradient are already formalised, and `ConvexOptAlg.Ellipsoid.theorem_2_4` supplies the convergence rate. The work that remains is (i) the run itself, (ii) its rational (square-root-free) formulation, and (iii) its compilation to a `PolyProgram` with a polynomial runtime bound.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170 (the MAXCUT SDP and its dual); Bubeck, arXiv:1405.4980v2, Thm 2.4 (ellipsoid convergence). The algorithmic core of QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix

open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **A polynomial-time machine that outputs a rational value together with a primal-dual
certificate pair whose duality gap is at most `1/10000` of the total edge weight.**

This is the algorithmic content of the Max-Cut SDP lower value: the reported rational `L G` is at
most the objective value at the feasible `X G`, and the gap to the dual bound
`(1/4)(Σ_{i,j} A(G)_{ij} + Σ_i lam i)` is within tolerance. The certificate pair is carried in the
statement on purpose: it forces the machine to actually solve the relaxation, not merely to output
a number that happens to be small. -/
theorem agm_sdp_certificate_program :
    ∃ (L : Input → ℚ≥0)
      (X : (G : Input) → Matrix (Fin G.n) (Fin G.n) ℝ)
      (lam : (G : Input) → Fin G.n → ℝ),
      Nonempty (Turing.TM2ComputableInPolyTime encodeRequest encodeValue
        (fun request : Input × List Bool => L request.1)) ∧
      ∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S ∧
        ModernConvex.Relaxations.IsUnitDiagPSD (X G) ∧
        (weightMatrix G + Matrix.diagonal (lam G)).PosSemidef ∧
        (L G : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G) (X G) ∧
        (1 / 4) * ((∑ i, ∑ j, weightMatrix G i j) + ∑ i, lam G i) - (L G : ℝ)
          ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry

end QuantumMaxCutEnergy
