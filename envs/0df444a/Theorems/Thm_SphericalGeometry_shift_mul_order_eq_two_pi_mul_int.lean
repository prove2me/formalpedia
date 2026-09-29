-- Prove2me | Theorems.Thm_SphericalGeometry_shift_mul_order_eq_two_pi_mul_int
-- name    : SphericalGeometry.shift_mul_order_eq_two_pi_mul_int
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:40:27.54299+00:00
-- url     : https://prove2.me/theorems/1759ac21-e96d-446a-929d-c55aa430aea7
-- title:
--   A finite-order symmetry advancing a great circle forces a rational shift
-- statement:
--   Suppose a self-map $w$ of an inner product space advances a great circle by a fixed angle,
--   $$\gamma_{v_1,v_2}(s+T)=w\bigl(\gamma_{v_1,v_2}(s)\bigr)\quad\text{for all }s,$$
--   where $\|v_1\|=1$ and $\langle v_1,v_2\rangle=0$, and suppose $w$ has finite order $k$, in the sense that its $k$-th iterate is the identity. Then
--   $$kT\in 2\pi\mathbb Z .$$
--
--   **Role.** This is the arithmetic conclusion of the closed-billiards-path analysis. In the application $w$ is an element of the finite Weyl group and $T=2\pi\alpha/m$ is the shift realized along the image of the unit circle; the lemma then says $\alpha$ is a rational number whose denominator divides the order of $w$, and hence divides the order of the Weyl group. That is exactly the constraint on the possible orders of a harmonic map into a Euclidean building.
--
--   **Proof.** Iterating the equivariance $n$ times gives $\gamma(s+nT)=w^{n}(\gamma(s))$, by induction on $n$. At $n=k$ the right-hand side is $\gamma(s)$, so the path is $kT$-periodic. Evaluating at $s=0$, where $\gamma(0)=v_1$, gives
--   $$\cos(kT)\,v_1+\sin(kT)\,v_2=v_1 .$$
--   Pairing with $v_1$ and using $\langle v_1,v_1\rangle=1$, $\langle v_2,v_1\rangle=0$ leaves $\cos(kT)=1$, whence $kT$ is an integer multiple of $2\pi$.
--
--   **Formalization note.** Only $\|v_1\|=1$ and orthogonality are used; the norm of $v_2$ is irrelevant, since the argument extracts a single coefficient by pairing with $v_1$. The finiteness of the order is stated as an iterate condition rather than as a group power, so that the lemma applies to any self-map with that property.
-- source:
--   The arithmetic step of the closed-billiards-path analysis in Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem shift_mul_order_eq_two_pi_mul_int {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : E → E) (v1 v2 : E) (h1 : ‖v1‖ = 1)
    (h12 : inner ℝ v1 v2 = (0:ℝ)) (T : ℝ) (k : ℕ)
    (hord : ∀ x : E, w^[k] x = x)
    (heq : ∀ s : ℝ,
      greatCirclePath v1 v2 (s + T) = w (greatCirclePath v1 v2 s)) :
    ∃ m : ℤ, (k : ℝ) * T = 2 * Real.pi * m := by sorry

end SphericalGeometry
