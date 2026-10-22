-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_5
-- name    : QMaxCutSDP.Rounding.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:02.860002+00:00
-- url     : https://prove2.me/theorems/91f0e39e-a338-4239-aada-c35647af838c
-- title:
--   Lemma 5 — probability that an edge is cut
-- statement:
--   Let $v$ be a feasible solution of (S). Choose $a\in\{1,2,3\}$ uniformly and round the signs of a random direction against the vectors $v_{i,a}$. For an edge $(i,j)$, let $z_i,z_j$ be the resulting bits and let $\gamma_{ij}=-(v_0+v_{ij})\cdot v_0/(\|v_0+v_{ij}\|\|v_0\|)$. Then
--   $$\Pr[z_i\ne z_j]\ge\frac{\alpha_{\mathrm{GW}}}{3}(2+\gamma_{ij}),$$
--   where $\alpha_{\mathrm{GW}}$ is the Goemans–Williamson constant. This is the rounding probability used in the edge-energy estimate.
--
--   **Formalization Note** The random direction is represented by a standard Gaussian vector, which has the same sign pattern as a sphere-uniform direction. The claim holds for every feasible solution; optimality is not used.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 10, Lemma 5, eq. (14); proof pp. 14–15

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 5, p. 10, equation (14), the hyperplane cut probability. -/
theorem lemma_5 {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : SDPVec n N) (hv : IsSFeasible v) (i j : Fin n)
    (hij : G.Adj i j) :
    alphaGW / 3 * (2 + gammaE v i j) ≤
      (1 / 3 : ℝ) * ∑ a : Fin 3,
        ((stdGaussian N) {r | bits v a r i ≠ bits v a r j}).toReal := by sorry
end QMaxCutSDP.Rounding
