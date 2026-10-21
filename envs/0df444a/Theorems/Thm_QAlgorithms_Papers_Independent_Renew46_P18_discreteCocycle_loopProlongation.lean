-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P18_discreteCocycle_loopProlongation
-- name    : QAlgorithms.Papers.Independent.Renew46.P18.discreteCocycle_loopProlongation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:19:18.750545+00:00
-- url     : https://prove2.me/theorems/de120aea-b594-47a5-85c9-7f9d8f36280a
-- title:
--   A discrete generalized cocycle gives the explicit loop prolongation
-- statement:
--   Let $H$ be a discrete group, $Z$ a discrete abelian group, and $A\le Z$ an additive subgroup, with its inclusion into $Z$ understood. Let $F:H^2\to Z$ and $\Theta:H^3\to A$ be normalized cochains, so they vanish when any argument is the identity, and suppose $d_{\mathrm{gp}}F=\Theta$ and $d_{\mathrm{gp}}\Theta=0$, with trivial coefficient action. Here $d_{\mathrm{gp}}F(g,h,k)=F(h,k)-F(gh,k)+F(g,hk)-F(g,h)$.
--
--   The multiplication
--   $$
--   (z,g)\cdot(w,h)=(z+w+F(g,h),gh)
--   $$
--   turns $Z\times H$ into a loop with unit $(0,e)$. Write $q:Z\to Z/A$ for the canonical quotient. The multiplication induced by $qF$ turns $B=(Z/A)\times_{qF}H$ into a group, and
--   $$
--   \varphi:Z\times_F H\longrightarrow B,\qquad (z,g)\longmapsto(q(z),g)
--   $$
--   is a loop prolongation by the embedded subgroup $a\mapsto(a,e)$. Explicitly, it is a surjective loop homomorphism; all associators lie in $A$, commute with the kernel, and are the identity if any argument lies in the kernel, and $A$ commutes with the whole loop. The associator convention is $x(yz)=\mathcal A(x,y,z)((xy)z)$, and its value on $x=(z,g)$, $y=(w,h)$, $z'=(v,k)$ is $(\Theta(g,h,k),e)$. Consequently the associated normalized group 3-cocycle on $B$ is
--   $$
--   \Theta_B((\bar z,g),(\bar w,h),(\bar v,k))=\Theta(g,h,k).
--   $$
--   This construction interprets the generalized cocycle as an actual loop prolongation with its specified quotient map and associativity obstruction.
-- source:
--   Categorified central extensions, \'etale Lie 2-groups and Lie's Third Theorem for locally exponential Lie algebras, arXiv:0812.1673v3, PDF p. 12, Lemma II.3: discrete cocycle loop prolongation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18

namespace QAlgorithms.Papers.Independent.Renew46.P18

universe u v w x

/-- Lemma II.3, PDF pp. 12–13: the explicit twisted loop and canonical
quotient form a loop prolongation, whose associated cocycle is Theta
inflated along the projection to H. The sign follows Remark II.2;
the displayed calculation in the proof on p. 12 reverses this sign. -/
theorem discreteCocycle_loopProlongation
    {H : Type u} {Z : Type v} [Group H] [AddCommGroup Z]
    (A : AddSubgroup Z) (F : H → H → Z) (theta : H → H → H → A)
    (h : IsDiscreteGeneralisedCocycle A F theta) :
    IsLoopProlongation (twistedMul F) (0, 1)
      (twistedMul (quotientCocycle A F)) (0, 1)
      (twistedRightInverse (quotientCocycle A F))
      (twistedProjection A) (coefficientInclusion A) (inflatedTheta A theta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P18
