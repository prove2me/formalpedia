-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P10_flow_periodic_ellipses
-- name    : QAlgorithms.Papers.Independent.Claimed50.P10.flow_periodic_ellipses
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:21:15.860134+00:00
-- url     : https://prove2.me/theorems/16401fe0-52b9-426c-8d4b-005f4f976fee
-- title:
--   Periodicity, two elliptic invariants, and coordinate-pair rotations
-- statement:
--   Let $n>0$ be an integer, put $k=\sqrt7$, and use double phase-space coordinates $z=(x,p,\xi_x,\xi_p)\in\mathbb R^{4n}$. Let $s(t)=e^{tM}$ be the Hamiltonian flow of $H=2\xi_x\cdot\xi_p-x\cdot\xi_x-p\cdot\xi_p+4x\cdot p$, where $M$ is its Hamilton matrix in that coordinate order. Define $Q(u,v)=2\lVert u\rVert_2^2+\lVert v\rVert_2^2-u\cdot v$. For every real $t$ and every $z$, writing $s(t)z=(x_t,p_t,\xi_{x,t},\xi_{p,t})$, one has
--
--   $$
--   s(t+2\pi/k)z=s(t)z,\qquad Q(x_t,\xi_{p,t})=Q(x,\xi_p),\qquad Q(p_t,\xi_{x,t})=Q(p,\xi_x).
--   $$
--
--   The ellipse geometry is expressed coordinatewise as follows. Put $E(u,v)=(ku,2v-u)$ and $R(a)(q,r)=(q\cos a+r\sin a,r\cos a-q\sin a)$. For every coordinate $j$,
--
--   $$
--   E(x_{t,j},\xi_{p,t,j})=R(kt)E(x_j,\xi_{p,j}),\qquad E(p_{t,j},\xi_{x,t,j})=R(kt)E(p_j,\xi_{x,j}).
--   $$
--
--   Since $\lVert E(u,v)\rVert_2^2=4(2u^2+v^2-uv)$, these are rotations along the two families of coordinate-pair ellipses. A zero pair is stationary. This formulation identifies the periodic motion and its conserved level surfaces without claiming that an orbit fills a higher-dimensional level surface.
-- source:
--   Metaplectic formulation of the Wigner transform and applications, arXiv:1401.3388v1, PDF p. 5, Remark 5: periodicity and elliptic invariants

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P10

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P10

/-- PDF p.5, Remark 5, using the independently constructed Hamiltonian flow.
It has period 2*pi/sqrt(7), preserves both displayed level surfaces, and rotates
each (x_j,xi_p_j) and (p_j,xi_x_j) pair along its ellipse. Zero pairs remain
stationary; no claim says an orbit fills a higher-dimensional level surface. -/
theorem flow_periodic_ellipses {n : ℕ} (hn : 0 < n) :
    (∀ (theta : ℝ) (z : DoublePhaseSpace n),
      hamiltonianFlow (theta + 2 * Real.pi / Real.sqrt 7) z =
        hamiltonianFlow theta z) ∧
    (∀ (theta : ℝ) (z : DoublePhaseSpace n),
      ellipticEnergy ((hamiltonianFlow theta z) 0) ((hamiltonianFlow theta z) 3) =
        ellipticEnergy (z 0) (z 3) ∧
      ellipticEnergy ((hamiltonianFlow theta z) 1) ((hamiltonianFlow theta z) 2) =
        ellipticEnergy (z 1) (z 2) ∧
      (∀ j : Fin n,
        ellipticCoordinates ((hamiltonianFlow theta z) 0 j)
            ((hamiltonianFlow theta z) 3 j) =
          clockwiseRotation (Real.sqrt 7 * theta) (ellipticCoordinates (z 0 j) (z 3 j)) ∧
        ellipticCoordinates ((hamiltonianFlow theta z) 1 j)
            ((hamiltonianFlow theta z) 2 j) =
          clockwiseRotation (Real.sqrt 7 * theta) (ellipticCoordinates (z 1 j) (z 2 j)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P10

end
