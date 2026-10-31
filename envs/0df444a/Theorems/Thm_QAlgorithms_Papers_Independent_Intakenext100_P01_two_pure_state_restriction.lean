-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_two_pure_state_restriction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.two_pure_state_restriction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:10:23.560128+00:00
-- url     : https://prove2.me/theorems/4a9f11d2-5f72-4097-9059-10a4a801cfb7
-- title:
--   Two pure preimages and a vertex
-- statement:
--   Let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel with $d,n\ge1$. Let $x,y\in\mathbb C^d$ be unit vectors with $xx^*\ne yy^*$, and suppose $T(xx^*)$ is a vertex of the physical image of $T$. A vertex here is a point whose supporting hyperplanes intersect only at that point, as in Definition 3.1. Put $H=\operatorname{span}_{\mathbb C}\{x,y\}$. There is a unit vector $z\in H$ orthogonal to $x$ such that, for every operator $A$ supported on $H$,
--   $$T(A)=\langle x,Ax\rangle T(xx^*)+\langle z,Az\rangle T(zz^*).$$
--   Moreover, if $T(yy^*)$ is a vertex different from $T(xx^*)$, then $\langle x,y\rangle=0$.
--
--   This is the two-dimensional geometric restriction underlying the canonical decomposition.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 4, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Lemma 3.2, PDF pp.4–5: two-pure-state restriction and orthogonality of distinct
vertex preimages; different states are distinguished by projectors. -/
theorem two_pure_state_restriction {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) : TwoPureGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
