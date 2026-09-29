-- Prove2me | Theorems.Thm_Rep_indBotr_indBotMk
-- name    : Rep.indBotr_indBotMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/eafed99c-cc60-5d24-a6c2-c6bc36599dda
-- title:
--   Value of the retraction Ind₁^GRes A → A on generators
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $A$ be a $k$-linear representation of $G$ (an object of `Rep k G`), and let $g \in G$ and $a \in A$. Write $A.\mathrm{indBot}$ for the representation obtained by inducing along the inclusion of the trivial subgroup $\bot \le G$ the restriction of $A$ to $\bot$, realised as the coinvariants of $k[G] \otimes_k A$ for the action of $\bot$; let $A.\mathrm{indBotMk}\,g : A \to A.\mathrm{indBot}$ be the $k$-linear map given by `Representation.IndV.mk` at the element $g$, so that $a$ is sent to the class of $\delta_g \otimes a$; and let $A.\mathrm{indBotr} : A.\mathrm{indBot} \to A$ be the $k$-linear map descending from the tensor-product lift of $(f, a) \mapsto f(1) \cdot a$, where the coefficient of $f \in k[G]$ at $1 \in G$ is taken via the coefficient equivalence to finitely supported functions and evaluation at $1$, the descent being legitimate because $\bot$ has $1$ as its only element. The assertion is the identity $A.\mathrm{indBotr}(A.\mathrm{indBotMk}\,g\,a) = (\mathrm{Finsupp.single}\,g\,1)(1) \cdot a$ in $A$, that is, the retraction sends the class of $\delta_g \otimes a$ to $a$ when $g = 1$ and to $0$ otherwise.
--
--   This records the value on the standard generators of the $k$-linear retraction of the induced representation $\mathrm{Ind}_1^G\,\mathrm{Res}_1^G A$ onto $A$, the basic ingredient for dimension shifting with induced (equivalently coinduced) modules. It is used to prove that the retraction splits the canonical inclusion of $A$, via [`Rep.indBotr_indBotIota`](thm.html#Rep.indBotr_indBotIota).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotr_indBotMk.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBotr_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotr (A.indBotMk g a) = (Finsupp.single g (1 : k)) 1 • a := by sorry
