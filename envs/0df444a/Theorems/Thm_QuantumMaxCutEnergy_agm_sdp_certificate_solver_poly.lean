-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_certificate_solver_poly
-- name    : QuantumMaxCutEnergy.agm_sdp_certificate_solver_poly
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-04T19:13:52.112933+00:00
-- url     : https://prove2.me/theorems/8111a220-f606-4b45-8780-aceb272b73cb
-- statement:
--   This is the solver core of the classical numerical routine for the Max-Cut semidefinite relaxation, stated for an explicit polynomial-time function on edge lists, with the Turing-machine input/output plumbing removed.
--
--   Let $G$ be a graph on vertices $\{0,\dots,n-1\}$ with nonnegative rational weights $w_{ij}$ for $i<j$. Its canonical edge list $E(G)$ lists the triples $((i,j),w_{ij})$ for all pairs $i<j$ in lexicographic order. Let $A=A(G)$ be the symmetric weight matrix with $A_{ij}=A_{ji}=w_{ij}$ for $i<j$ and $A_{ii}=0$, and let $W=\sum_{i<j}w_{ij}$. The Max-Cut SDP of Ben-Tal–Nemirovski (4.3.15) maximizes
--
--   $$
--   f_A(X)=\frac14\sum_{i,j=1}^n A_{ij}\,(1-X_{ij})
--   $$
--
--   over real symmetric $X\succeq0$ with unit diagonal.
--
--   **Theorem.** There is a function $\mathrm{Solve}$ that sends an edge list to a pair $(X,y)$, where $X$ is a list of rational rows and $y$ is a list of rationals. $\mathrm{Solve}$ is polynomial-time computable in the runtime library's `Poly` sense (a Boolean-stack program with polynomial running time on the library's canonical encodings). For every weighted graph $G$, write $X$ for the $n\times n$ rational matrix read from the rows of $\mathrm{Solve}(E(G))$ and $y$ for the length-$n$ vector read from its second component, with missing entries read as $0$. Then:
--
--   1. $X$ is SDP-feasible: $X\succeq0$ and $X_{ii}=1$ for all $i$;
--   2. $y$ is dual feasible: $\operatorname{Diag}(y)+\frac14A\succeq0$;
--   3. the duality gap is small:
--
--   $$
--   \frac14\sum_{i,j}A_{ij}+\sum_i y_i-f_A(X)\;\le\;\frac{W}{10000}.
--   $$
--
--   The solver therefore outputs exact rational primal and dual certificates for the classical Max-Cut SDP to additive accuracy $W/10000$. This is the only algorithmic ingredient of the numerical lower-value routine in the classical $0.53$ estimator of Anshu–Gosset–Morenz (TQC 2020, Theorem 3). Evaluating $f_A(X)$, the sign condition $f_A(X)\ge0$, and the compilation to the campaign's Turing-machine encodings are handled separately.
--
--   The statement includes $n=0$, empty edge sets and zero weights.
--
--   **Formalization Note** `Poly` is `OAI.MetricKMedian.Binary.Automatic.Poly` from the imported runtime definition, using its `Coding` encodings for natural numbers, rationals, pairs and lists. $E(G)$ is `QMCNumericRuntime.inputEdges G`. Matrix rows are read with `List.getD`, with default $0$.
-- source:
--   Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, TQC 2020, Theorem 3 (https://doi.org/10.4230/LIPIcs.TQC.2020.7); Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, (4.3.15) p.170; Grotschel-Lovasz-Schrijver, Geometric Algorithms and Combinatorial Optimization, Springer 1988; Alizadeh, SIAM J. Optim. 5 (1995) 13-51

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_sdp_certificate_solver_poly :
    ∃ Solve : List QMCNumericRuntime.NumericEdge → List (List ℚ) × List ℚ,
      OAI.MetricKMedian.Binary.Automatic.Poly Solve ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        ModernConvex.Relaxations.IsUnitDiagPSD
          (Matrix.of fun i j : Fin G.n =>
            ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ∧
        (Matrix.diagonal (fun i : Fin G.n =>
            (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ)) +
          (1 / 4 : ℝ) • (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧
        (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) +
          ∑ i : Fin G.n, (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ) -
          ModernConvex.Relaxations.maxcutRelaxationObjective
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
            (Matrix.of fun i j : Fin G.n =>
              ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ))
          ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
