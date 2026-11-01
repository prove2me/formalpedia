-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P71_targetBraiding_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P71.targetBraiding_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:42:43.197046+00:00
-- url     : https://prove2.me/theorems/66b12773-db28-4953-8fef-55b33c83d3dc
-- title:
--   Claim 8.5.3: uniqueness of a descended target braiding
-- statement:
--   Let $H_\bullet$ and $G_\bullet$ be right crossed modules of group sheaves on a subcanonical site $S$. Fix a braiding $c_H$ on $H_\bullet$ and two braidings $c_G,c'_G$ on $G_\bullet$. Suppose $E$ is a braided butterfly from $(H_\bullet,c_H)$ to $(G_\bullet,c_G)$ and $E'$ is a braided butterfly from $(H_\bullet,c_H)$ to $(G_\bullet,c'_G)$. Suppose there is an isomorphism of their underlying butterflies and $j:E\to G_0$ is locally epimorphic. Then the actual target brackets agree:
--
--   $$
--   c_G=c'_G.
--   $$
--
--   This is uniqueness of the descended bracket itself, which permits gluing target Picard structures.
-- source:
--   Butterflies I: morphisms of 2-group stacks, arXiv:0808.3627v2, PDF p. 76, Claim 8.5.3: uniqueness of a descended target braiding

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71

namespace QAlgorithms.Papers.Independent.Intakenext100.P71

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]

variable {J : GrothendieckTopology C}

/-- Claim 8.5.3, arXiv:0808.3627v2, PDF p.76.
The target bracket for Eprime is cGprime, correcting the repeated cG in
the printed parenthesis. Isomorphic butterflies with locally epimorphic
j determine the same target bracket, not merely isomorphic classes. -/
theorem targetBraiding_unique [J.Subcanonical]
    {H G : RightCrossedModule.{u, v, w} J}
    (E Eprime : Butterfly H G) (cH : Braiding H) (cG cGprime : Braiding G)
    (hE : E.IsBraided cH cG) (hEprime : Eprime.IsBraided cH cGprime)
    (e : ButterflyIso E Eprime) (hlocal : IsLocalEpi E.j) :
    cG.bracket = cGprime.bracket := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P71
