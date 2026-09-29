-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG
-- name    : ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/0b9157e4-6e00-5a30-b46f-250676693841
-- title:
--   Global sections of M̃(d) come from M_d for dgg 0
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $n$ be a natural number, and let $D$ be a [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18), that is, an $R$-module $D.M$ together with a family of submodules $D.\mathrm{grade}(d)$ indexed by $d \in \mathbb{Z}$ and $R$-linear maps $x_0,\dots,x_n$ carrying $D.\mathrm{grade}(d)$ into $D.\mathrm{grade}(d+1)$ and commuting with one another. Assume $D$ satisfies `IsFG`, i.e. it admits a `Presentation`: a finite index type $J$, degrees $d_0 : J \to \mathbb{Z}$, and a morphism of graded modules from $\bigoplus_{k \in J} \mathrm{FD}(d_0 k)$ to $D$ which is surjective in every degree. Then there is $d_0 \in \mathbb{Z}$ such that for every $d \ge d_0$ and every $c$ in $H^0$ of the shifted module $\mathrm{shift}\,D\,d$ (whose degree-$e$ piece is $D.\mathrm{grade}(e+d)$) — by definition the kernel of the Čech differential $d^0$ on $0$-cochains, so $c$ is a family of sections $c_s$ over the charts $\mathrm{img}(s)$, $s$ ranging over $\mathrm{Idx}\,n\,0$, whose pairwise restrictions agree — there exist $m \in D.\mathrm{grade}(d)$ and a proof $hm$ that $m$ lies in the degree-$\sum_j 0 = 0$ piece of $\mathrm{shift}\,D\,d$ such that for every $s$ the component $c_s$ equals the class of the fraction with all denominator exponents zero and numerator $m$, i.e. $m/1$, in the module of sections of $\mathrm{shift}\,D\,d$ over $\mathrm{img}(s)$.
--
--   This is Serre's theorem that for a finitely generated graded module over a polynomial ring over a Noetherian ring the natural map $M_d \to H^0(\mathbb{P}^n_R, \widetilde{M}(d))$ is surjective for all sufficiently large $d$, in the Čech formulation on the standard cover by the charts $D_+(x_i)$. It is used in the treatment of closed immersions into projective space, where homogeneous equations must be produced from given global sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
        ∃ m : D.M, m ∈ D.grade d ∧
          ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                  ⟨0, fun _ _ => rfl, m, hm⟩ := by sorry
