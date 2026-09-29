-- Prove2me | Theorems.Thm_PDivisibleGroup_associated_discr_level_of_hasDimension_of_ringOfIntegers
-- name    : PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/7d6e23aa-47ea-5076-9742-e8d151395fe5
-- title:
--   Discriminant of a level of a p-divisible group over mathcal O_K
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\mathbb Q_p \subseteq \overline{\mathbb Q}_p$ (the chosen algebraic closure `PadicAlgCl p`) with $K/\mathbb Q_p$ finite, and write $\mathcal O_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb Z_p$-subalgebra of $\overline{\mathbb Q}_p$ obtained by intersecting the integral closure of $\mathbb Z_p$ in $\overline{\mathbb Q}_p$ with $K$. Let $G$ be a $p$-divisible group over $\mathcal O_K$ of height $h$ in the project's sense: a family of commutative rings $G.\mathrm{level}\,v$ ($v \in \mathbb N$), each a cocommutative Hopf algebra over $\mathcal O_K$ that is finite and free as an $\mathcal O_K$-module of rank $p^{vh}$, together with surjective coalgebra–algebra maps $G.\mathrm{level}(v+1) \to G.\mathrm{level}\,v$ whose kernels are the ideals $\mathrm{torsionIdeal}$ of the augmentation ideal of $G.\mathrm{level}(v+1)$ at $p^v$. Assume $G.\mathrm{HasDimension}\,n$, i.e. for every $v$ the cotangent module of the augmentation ideal of $G.\mathrm{level}\,v$ is isomorphic, as an $\mathcal O_K$-module, to $(\mathcal O_K/(p^v))^n$. Then for every $v$ and every finite $\mathcal O_K$-basis $b$, indexed by a finite type $\iota$, of $G.\mathrm{level}\,v$, the discriminant $\mathrm{disc}_{\mathcal O_K}(b)$ is associated in $\mathcal O_K$ (equal up to a unit) to $p^{\,n v p^{vh}}$.
--
--   This is Tate's computation of the discriminant of the $v$-th level of a $p$-divisible group over the ring of integers of a finite extension of $\mathbb Q_p$, the quantitative input behind the statement that the Tate module functor is fully faithful. It is used in the proof that a map of $p$-divisible groups inducing a bijection on Tate modules is a bijection at every level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_associated_discr_level_of_hasDimension_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ} (hn : G.HasDimension n)
    (v : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (PadicAlgCl.ringOfIntegers p K) (G.level v)) :
    Associated (Algebra.discr (PadicAlgCl.ringOfIntegers p K) b)
      (((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ (n * v * p ^ (v * h))) := by sorry
