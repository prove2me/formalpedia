-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d838794a-9012-5d80-9fa0-d3986c15eae1
-- title:
--   Atkin–Lehner idèle raising an Eichler order to level Nq
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime such that [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q'`](def/QuaternionAlgebra_EichlerOrder.html#L87) holds, i.e. $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q'\in v$. Let $R$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is Eichler of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with $[\Lambda_1:R]=N$ as additive groups, and let $q$ be a prime with $q\neq q'$ and $q\nmid N$. Then there is a unit $n$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ such that, writing $S=$ [`CerednikDrinfeld.meetOrder R n`](def/CerednikDrinfeld_ClassSetGraph.html#L15) $=R\cap(\text{the elements of }\mathbb{H}[\mathbb{Q},a,b]\text{ lying in }n\widehat{R}n^{-1})$: (i) $S$ is Eichler of level $Nq$; (ii) $n\in$ [`QuaternionAlgebra.primeHeckeSet R q`](def/QuaternionAlgebra_ClassSetHecke.html#L109), that is $n\in\widehat{R}$, $qn^{-1}\in\widehat{R}$, $n^{-1}\notin\widehat{R}$ and $q^{-1}n\notin\widehat{R}$, where $\widehat{R}$ denotes [`Submodule.finiteAdeleBox R`](def/Submodule_FiniteAdeleBox.html#L14); (iii) $n$ normalises $S$, i.e. [`Submodule.conjByFiniteIdele S n = S`](def/Submodule_FiniteAdeleBox.html#L31); (iv) on the double coset set $\mathbb{H}^\times\backslash(\mathbb{H}\otimes\mathbb{A}_f)^\times/\widehat{S}^\times$, where $\widehat{S}^\times=$ [`Submodule.finiteIdeleStabilizer S`](def/Submodule_FiniteAdeleBox.html#L26), right translation by $n$ composed with itself is the identity; and (v) $n^2=q\cdot u$ for some $u\in\widehat{S}^\times$, with $q$ the central idèle image of the unit $q\in\mathbb{Q}^\times$.
--
--   This is the adelic construction of the Atkin–Lehner element at an auxiliary prime $q$ which is split in the definite quaternion algebra and coprime to the Eichler level: locally at $q$ one takes the antidiagonal matrix $\begin{pmatrix}0&1\\q&0\end{pmatrix}$ in $M_2(\mathbb{Z}_q)\cong R_q$ and the trivial idèle elsewhere, so that the meet order is Iwahori at $q$. It supplies the level-raising step and the involution on the class set used in the Čerednik–Drinfeld torsion data and in the decomposition of Hecke elements at a prime not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hqq' : q ≠ q') (hqN : ¬ q ∣ N) :
    ∃ n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      QuaternionAlgebra.IsEichlerOrder (CerednikDrinfeld.meetOrder R n) (N * q) ∧
      n ∈ QuaternionAlgebra.primeHeckeSet R q ∧
      Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder R n) n = CerednikDrinfeld.meetOrder R n ∧
      (∀ x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)),
        CerednikDrinfeld.classSetShift _ n (CerednikDrinfeld.classSetShift _ n x) = x) ∧
      ∃ u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n),
        n * n = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero))) * u := by sorry
