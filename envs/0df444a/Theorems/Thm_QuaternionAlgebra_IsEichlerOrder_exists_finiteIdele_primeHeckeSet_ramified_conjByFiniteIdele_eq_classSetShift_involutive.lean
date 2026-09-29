-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4a49ee9f-abbd-5125-9bc3-3ffcbda08325
-- title:
--   Atkin–Lehner idele at a ramified prime: involutive class-set shift
-- statement:
--   Let $a,b\in\mathbb Q$ and let $p$ be an odd prime such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsDefiniteRamifiedExactlyAt a b p`, i.e. $a<0$, $b<0$, and for a finite place $w$ of $\mathbb Q$ the algebra $\mathbb H\otimes_{\mathbb Q}\mathbb Q_w$ has all nonzero elements invertible exactly when $p$ lies in $w$. Let $R\subseteq\mathbb H$ be a $\mathbb Z$-submodule which is an Eichler order of level $N$, that is, $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$ with relative index $N$ of $R$ in $\Lambda_1$, and let $v$ be a finite place containing $p$. Then there is a unit $\varpi$ of $\mathbb H\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{f}$ with: (i) component $1$ at every place $w$ not containing $p$; (ii) $\varpi^{2}=p\cdot u$, where $p$ is the diagonal idele coming from the unit $p$ of $\mathbb H$, and $u$ lies in the stabiliser of the adelic box of $X$ for every order $X$ of $\mathbb H$ with `localBox X v = localBox R v`; and (iii) for every such $X$: $\varpi$ lies in `primeHeckeSet X p`, i.e. $\varpi\in\widehat X$, $p\varpi^{-1}\in\widehat X$, $\varpi^{-1}\notin\widehat X$ and $p^{-1}\varpi\notin\widehat X$; conjugation of $X$ by $\varpi$ returns $X$; the right shift by $\varpi$ on the class set $\mathbb H^{\times}\backslash(\mathbb H\otimes\mathbb A^{f})^{\times}/\widehat X^{\times}$ (where $\widehat X^\times$ is the adelic stabiliser of $X$) satisfies `classSetShift _ ϖ (classSetShift _ ϖ x) = x` for all $x$; and for every idele $m$ whose component at $v$ and whose inverse component at $v$ lie in `localBox R v`, one has $m\varpi=\varpi m c$ for some $c$ in the stabiliser of $X$, and, if conjugation of $X$ by $m$ returns $X$, the shifts by $\varpi$ and by $m$ commute on the class set.
--
--   This is the Atkin–Lehner element at the ramified prime of a definite quaternion algebra over $\mathbb Q$, realised as an idele supported at $p$ alone which is a local uniformiser for the box of $R$ at $v$ and which induces an involution of the class set; the formulation is uniform in all orders $X$ agreeing with $R$ locally at $v$, so that one element serves a whole tower of levels. It is used in the construction of the Čerednik–Drinfeld coset graph, in [`CerednikDrinfeld.CosetGraph.exists_quot_equiv_classSet_shift_forget_of_mumfordSideFrame`](thm.html#CerednikDrinfeld.CosetGraph.exists_quot_equiv_classSet_shift_forget_of_mumfordSideFrame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∃ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))) * u ∧
        ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
          u ∈ Submodule.finiteIdeleStabilizer X) ∧
      ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
        ϖ ∈ primeHeckeSet X p ∧
        Submodule.conjByFiniteIdele X ϖ = X ∧
        (∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
          classSetShift _ ϖ (classSetShift _ ϖ x) = x) ∧
        ∀ m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits R v →
          (∃ c ∈ Submodule.finiteIdeleStabilizer X, m * ϖ = ϖ * m * c) ∧
          (Submodule.conjByFiniteIdele X m = X →
            ∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
              classSetShift _ ϖ (classSetShift _ m x) = classSetShift _ m (classSetShift _ ϖ x)) := by sorry
