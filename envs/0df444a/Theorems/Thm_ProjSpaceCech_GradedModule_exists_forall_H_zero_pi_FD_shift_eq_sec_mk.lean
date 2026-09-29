-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk
-- name    : ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/2a35644c-8113-578e-8467-78867bf291bc
-- title:
--   Degree-d Čech 0-cocycles of bigoplus_k S(e_k) come from F_d
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number, $\iota$ a finite index type and $e : \iota \to \mathbb{Z}$. Write $F$ for [`ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L489), the graded module whose underlying module is the product over $k \in \iota$ of $S = R[x_0,\dots,x_n]$, whose $d$-th graded piece is the product of the pieces of $S$ in degree $d + e_k$ (the zero submodule in each component with $d + e_k < 0$), and whose operators are multiplication by the $x_j$ componentwise. The assertion is that there exists $d_1 \in \mathbb{Z}$ such that for every $d \ge d_1$ and every $c$ in $H^0$ of the shift of $F$ by $d$ — by definition an element of the kernel of the Čech differential [`ProjSpaceCech.GradedModule.d`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L386) in degree $0$, that is, a family assigning to each $s :$ [`ProjSpaceCech.Idx n 0`](def/AlgebraicGeometry_ProjSpaceCechTwist.html#L65) (a strictly monotone map $\mathrm{Fin}\,1 \to \mathrm{Fin}\,(n+1)$, i.e. a single chart index) a section of the shifted $F$ over `Idx.img n s`, subject to the agreement condition on overlaps — there is $f$ in the underlying module of $F$ lying in `F.grade d`, together with a proof $hf$ that $f$ lies in the grade of the shifted $F$ at $\sum_{j} 0 = 0$, such that for every chart $s$ the value $c(s)$ equals `sec.mk` applied to the fraction with all denominator exponents $0$, numerator $f$ and homogeneity witness $hf$. In other words, in large degree every Čech $0$-cocycle for the standard cover is, chart by chart, the fraction $f/1$ for one and the same element $f$ of $F_d = \bigoplus_k S_{d+e_k}$.
--
--   This is the Čech form of the classical computation $H^0(\mathbb{P}^n_R, \mathcal{O}(e)) = S_e$, in the shape needed here: surjectivity of $F_d \to \check H^0(\{D_+(x_i)\}, \widetilde{F(d)})$ for a finite sum of twists of the polynomial ring and all sufficiently large $d$ (the bound $d_1$ accounts for the case $n = 0$ and for negative twists). It is the free-module case from which the corresponding statement for finitely generated graded modules, [`ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG`](thm.html#ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk
    (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (e : ι → ℤ) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H
          (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0,
        ∃ f : (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).M,
          f ∈ (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).grade d ∧
          ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d).grade
              (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0))
                from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d)
                  (ProjSpaceCech.Idx.img n s) ⟨0, fun _ _ => rfl, f, hf⟩ := by sorry
