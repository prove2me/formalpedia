-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
-- name    : ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/c423d358-41e0-503e-820c-b29650c09c7a
-- title:
--   Dévissage for Čech H⁰ along a graded presentation
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number and $D$ a graded module over the projective-space Čech setup for $\mathbb{P}^n_R$ (a type $D.M$ with a grading $D.\mathrm{grade} : \mathbb{Z} \to$ submodules and commuting multiplication operators $x_j$ raising degree by one). Let $\sigma$ be a presentation of $D$: a finite index set $J$, degrees $d_0 : J \to \mathbb{Z}$, and a graded homomorphism from $\sigma.F = \prod_k \mathrm{FD}\,R\,n\,(d_0 k)$ to $D$ that is surjective in each degree; $\sigma.\mathrm{ker}$ is the graded module given by its kernel with the induced grading. Fix $d \in \mathbb{Z}$, and write $\mathrm{shift}\,E\,d$ for the graded module with $(\mathrm{shift}\,E\,d).\mathrm{grade}\,e = E.\mathrm{grade}(e+d)$. Assume (i) the Čech $H^1$ of $\mathrm{shift}\,\sigma.\mathrm{ker}\,d$ for the standard cover is a subsingleton, and (ii) every $c$ in the Čech $H^0$ of $\mathrm{shift}\,\sigma.F\,d$, i.e. every $0$-cochain in the kernel of the differential $d^0$, is of the following shape: there is a single $f \in \sigma.F.\mathrm{grade}\,d$, of degree $\sum_j 0$ in the shifted grading, such that for every $s : \mathrm{Idx}\,n\,0$ (a chart index) the component $c\,s$ in $\mathrm{sec}$ over $\mathrm{Idx.img}\,n\,s$ is the class of the fraction with all denominator exponents $0$ and numerator $f$. Then the same conclusion holds for $D$: every element $c$ of the Čech $H^0$ of $\mathrm{shift}\,D\,d$ arises from one $m \in D.\mathrm{grade}\,d$, with $c\,s$ equal to the class of $m/1$ on every chart $s$.
--
--   This is the dévissage step in the computation of the global sections of the sheaf attached to a graded module on $\mathbb{P}^n_R$ (as in Serre's FAC and Hartshorne III.5.2): chartwise representability of $0$-cocycles by a single element of the degree-$d$ piece passes from a free presenting module to the presented module, provided the first Čech cohomology of the shifted kernel vanishes. It is used by [`ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG`](thm.html#ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG), where the hypotheses are supplied for finitely generated graded modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
    {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (d : ℤ)
    (hK : Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.ker d) 1))
    (hF : ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.F d) 0,
      ∃ f : σ.F.M, f ∈ σ.F.grade d ∧
        ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift σ.F d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift σ.F d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift σ.F d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, f, hf⟩) :
    ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
      ∃ m : D.M, m ∈ D.grade d ∧
        ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, m, hm⟩ := by sorry
