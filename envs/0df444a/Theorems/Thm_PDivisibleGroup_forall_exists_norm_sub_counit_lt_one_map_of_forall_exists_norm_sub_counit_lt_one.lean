-- Prove2me | Theorems.Thm_PDivisibleGroup_forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
-- name    : PDivisibleGroup.forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/b166b1fe-2143-528d-8763-d937fa8141e7
-- title:
--   Points near the unit section push forward along Tψ
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\overline{\mathbb Q}_p/\mathbb Q_p$ (realised as `PadicAlgCl p`) that is finite over $\mathbb Q_p$, and let $\mathcal O =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) be the $\mathbb Z_p$-subalgebra of $\overline{\mathbb Q}_p$ obtained as the intersection of the integral closure of $\mathbb Z_p$ with $K$. Let $G$ and $Q$ be $p$-divisible groups over $\mathcal O$ of heights $h$, $h'$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): families of finite free cocommutative $\mathcal O$-Hopf algebras `level v` of rank $p^{v h}$ (resp. $p^{v h'}$) with surjective coalgebra-algebra transition maps `level (v+1) → level v` whose kernels are the $p^v$-torsion ideals. Let $\psi$ assign to each $v$ a bialgebra homomorphism $\psi_v \colon Q.\mathrm{level}\,v \to G.\mathrm{level}\,v$, and let $T\psi$ be a $\mathbb Z_p$-linear map between the Tate modules, where for an abelian group $M$ the Tate module consists of the sequences $(x_n)$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, applied to the groups of points $G.\mathrm{Points}(\overline{\mathbb Q}_p)$, the direct limit over $v$ of the convolution groups of $\mathcal O$-algebra maps $G.\mathrm{level}\,v \to \overline{\mathbb Q}_p$ (likewise for $Q$). Assume the levelwise compatibility `hTψ`: whenever a point $g$ at level $w$ represents the $n$-th component of $x$ in the direct limit, the $n$-th component of $T\psi\,x$ is represented by the point at level $w$ whose algebra map is $\psi_w$ followed by $g$. Assume further that every component of $x$ is represented by some point $g$ at some level $w$ satisfying $\lVert g(a) - \varepsilon(a)\rVert < 1$ for all $a$ in $G.\mathrm{level}\,w$, where $\varepsilon$ is the counit and its value is mapped into $\overline{\mathbb Q}_p$ by the structure map of $\mathcal O$. The conclusion is that every component of $T\psi\,x$ is likewise represented by a point $g'$ at some level $w$ with $\lVert g'(b) - \varepsilon(b)\rVert < 1$ for all $b$ in $Q.\mathrm{level}\,w$.
--
--   This is the statement that the condition of reducing to the unit section (points congruent to the counit modulo the maximal ideal of the valuation on $\overline{\mathbb Q}_p$) is stable under a homomorphism of $p$-divisible groups at the level of Tate modules. It is used in the assembly of the inertia-theoretic form of Tate's theorem on $p$-divisible groups, where the predicate has to be transported from one $p$-divisible group to another along $T\psi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (ψ : ∀ v : ℕ, Q.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
    (Tψ : TateModule p (G.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (Q.Points (PadicAlgCl p)))
    (hTψ : ∀ (x : TateModule p (G.Points (PadicAlgCl p))) (n w : ℕ) (g : G.Point (PadicAlgCl p) w),
        G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) n →
        ((Tψ x : TateModule p (Q.Points (PadicAlgCl p))) : ℕ → Q.Points (PadicAlgCl p)) n =
          Q.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Q.level w →ₐ[PadicAlgCl.ringOfIntegers p K] G.level w)))))
    (x : TateModule p (G.Points (PadicAlgCl p)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (g : G.Point (PadicAlgCl p) w),
      G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (x : ℕ → G.Points (PadicAlgCl p)) n ∧
      ∀ a : G.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    ∀ n : ℕ, ∃ (w : ℕ) (g : Q.Point (PadicAlgCl p) w),
      Q.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (Tψ x : ℕ → Q.Points (PadicAlgCl p)) n ∧
      ∀ a : Q.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1 := by sorry
