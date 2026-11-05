-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_certificate_tm2
-- name    : QuantumMaxCutEnergy.agm_classical_sdp_certificate_tm2
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-04T18:57:01.46028+00:00
-- url     : https://prove2.me/theorems/e47bfb9e-f939-43c1-94e6-e09315d5e9d8
-- statement:
--   This is the certificate form of polynomial-time solvability for the Max-Cut semidefinite relaxation, in the numerical setting of Anshu–Gosset–Morenz.
--
--   Let $G$ be a graph on vertices $\{0,\dots,n-1\}$ with nonnegative rational edge weights $w_{ij}$ for $i<j$, and let $A=A(G)$ be the symmetric $n\times n$ weight matrix with $A_{ij}=A_{ji}=w_{ij}$ for $i<j$ and $A_{ii}=0$. Write $W=\sum_{i<j}w_{ij}$ for the total weight. The Max-Cut SDP of Ben-Tal–Nemirovski (4.3.15) has objective
--
--   $$
--   f_A(X)=\frac14\sum_{i,j=1}^n A_{ij}\,(1-X_{ij}),
--   $$
--
--   maximized over real symmetric $X\succeq0$ with $X_{ii}=1$ for all $i$. A vector $y\in\mathbb R^n$ is dual feasible when
--
--   $$
--   \operatorname{Diag}(y)+\tfrac14 A\succeq0,
--   $$
--
--   and its dual value is $\frac14\sum_{i,j}A_{ij}+\sum_i y_i$, which equals $W/2+\sum_i y_i$.
--
--   **Theorem.** There is a function $L$ from weighted graphs to nonnegative rationals, computed by a polynomial-time multi-tape Turing machine (Mathlib's `Turing.TM2ComputableInPolyTime`) on the campaign input encoding `QuantumMaxCutEnergy.encodeRequest` (graph followed by an ignored random tape) and output encoding `QuantumMaxCutEnergy.encodeValue`, such that for every graph $G$ there exist a rational matrix $X$ and a rational vector $y$ with:
--
--   1. $X$ is feasible for the SDP: $X\succeq0$ and $X_{ii}=1$ for every $i$;
--   2. $y$ is dual feasible: $\operatorname{Diag}(y)+\frac14A\succeq0$;
--   3. $L(G)=f_A(X)$, that is, the output is the exact primal value of $X$;
--   4. the duality gap of the pair is small:
--
--   $$
--   \frac14\sum_{i,j}A_{ij}+\sum_i y_i-L(G)\;\le\;\frac{W}{10000}.
--   $$
--
--   The certificates $X,y$ are not part of the output; only their existence is asserted.
--
--   By weak duality, every such output satisfies $L(G)\le\mathrm{SDP}(G)\le L(G)+W/10000$, which is the numerical lower-value routine required by the classical $0.53$ energy-estimation algorithm of Anshu–Gosset–Morenz (TQC 2020, Theorem 3). The point of the certificate form is that both positive-semidefiniteness conditions and the gap are finite rational facts, so the analytic content (existence and characterization of the SDP value) is separated from the algorithmic content (an ellipsoid or interior-point solver with rounding to rational primal and dual points, as in Grötschel–Lovász–Schrijver, *Geometric Algorithms and Combinatorial Optimization*, Springer 1988, and Alizadeh, SIAM J. Optim. 5 (1995) 13–51, using strict feasibility of $X=I$ and of large $y$ for Slater's condition).
--
--   The statement includes empty graphs, $n=0$ and zero weights; then $X=I$, $y=0$ and $L(G)=0$ give gap $0$.
--
--   **Formalization Note** Rational certificates are coerced entrywise to real matrices. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` over $\mathbb R$, and feasibility is `ModernConvex.Relaxations.IsUnitDiagPSD`. The dual value is stated as $\frac14\sum_{i,j}A_{ij}+\sum_iy_i$ rather than $W/2+\sum_iy_i$.
-- source:
--   Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, TQC 2020, Theorem 3 (https://doi.org/10.4230/LIPIcs.TQC.2020.7); Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, (4.3.15) p.170; Grotschel-Lovasz-Schrijver, Geometric Algorithms and Combinatorial Optimization, Springer 1988; Alizadeh, SIAM J. Optim. 5 (1995) 13-51

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_classical_sdp_certificate_tm2 :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        ∃ (X : Matrix (Fin G.n) (Fin G.n) ℚ) (y : Fin G.n → ℚ),
          ModernConvex.Relaxations.IsUnitDiagPSD (X.map (fun q : ℚ => (q : ℝ))) ∧
          (Matrix.diagonal (fun i => (y i : ℝ)) + (1 / 4 : ℝ) •
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧
          (L G : ℝ) = ModernConvex.Relaxations.maxcutRelaxationObjective
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
            (X.map (fun q : ℚ => (q : ℝ))) ∧
          (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) +
            ∑ i, (y i : ℝ) - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
