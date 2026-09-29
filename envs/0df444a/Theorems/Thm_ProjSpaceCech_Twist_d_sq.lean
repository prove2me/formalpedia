-- Prove2me | Theorems.Thm_ProjSpaceCech_Twist_d_sq
-- name    : ProjSpaceCech.Twist.d_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/e160d3ab-c5fc-5c0c-91de-6dfbe8bef5de
-- title:
--   The twisted Čech differential squares to zero
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, let $d$ be an integer and let $i$ be a natural number. For $s \in$ `Idx n i` — an index datum consisting of a map of finite ordinals together with a proof that it is strictly monotone, so that `Idx.img n s` is the finite set of indices it picks out of the standard cover of $\mathbb{P}^n_R$ — the $i$-cochain module `Twist.cochain R n d i` is the product $\prod_{s}$ `Twist.Sec R n d (Idx.img n s)` of the section modules attached to those index sets, each a free $R$-module on the monomial index type `Twist.Mon n d K`. For $s \in$ `Idx n (i+1)` and $j \in \mathrm{Fin}(i+2)$, the face `Idx.face n s j` is $s$ precomposed with `Fin.succAbove j` (deletion of the $j$-th entry, again strictly monotone), and `Twist.faceRes R n d s j` is the $R$-linear restriction map `Finsupp.lmapDomain` along the inclusion `Twist.Mon.incl` of monomial index types induced by `Idx.img n (Idx.face n s j) ⊆ Idx.img n s`. The differential `Twist.d R n d i` is the $R$-linear map sending a cochain $f$ to the cochain whose value at $s$ is $\sum_{j \in \mathrm{Fin}(i+2)} (-1)^{j}\,\mathrm{res}\, f(\mathrm{face}\,s\,j)$. The assertion is that the composite of `Twist.d R n d i` followed by `Twist.d R n d (i+1)` is the zero linear map from `Twist.cochain R n d i` to `Twist.cochain R n d (i+2)`.
--
--   This is the cochain-complex identity $d^{i+1}\circ d^{i}=0$ for the alternating Čech complex of the Laurent-monomial model of $\mathcal{O}(d)$ on the standard cover of $\mathbb{P}^n_R$, so that the family of modules `Twist.cochain R n d i` with the maps `Twist.d` forms a complex. It is used in the comparison of the twisted Čech cohomology with the graded-module description, via [`ProjSpaceCech.GradedModule.nonempty_HEquiv_FD`](thm.html#ProjSpaceCech.GradedModule.nonempty_HEquiv_FD).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_Twist_d_sq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.Twist.d_sq (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    ProjSpaceCech.Twist.d R n d (i + 1) ∘ₗ ProjSpaceCech.Twist.d R n d i = 0 := by sorry
