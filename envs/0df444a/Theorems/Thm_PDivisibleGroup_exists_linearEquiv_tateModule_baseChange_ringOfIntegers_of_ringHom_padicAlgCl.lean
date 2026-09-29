-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
-- name    : PDivisibleGroup.exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f775c06b-5904-5279-b940-fa9432d8a2e3
-- title:
--   Transport of Tate modules along an embedding ℚ̄→ℚ̄ₚ
-- statement:
--   Fix a prime $p$, a commutative ring $O$ equipped with an algebra map to $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ`, a valuation subring $P$ of $\overline{\mathbb Q}$, and an intermediate field $K$ of $\overline{\mathbb Q}_p/\mathbb Q_p$ finite over $\mathbb Q_p$, with an $O$-algebra structure on $\mathcal O_K=$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) (the intersection of the integral closure of $\mathbb Z_p$ in $\overline{\mathbb Q}_p$ with $K$). Let $\iota\colon\overline{\mathbb Q}\to\overline{\mathbb Q}_p$ be a ring homomorphism such that the composites $O\to\mathcal O_K\hookrightarrow\overline{\mathbb Q}_p$ and $O\to\overline{\mathbb Q}\xrightarrow{\iota}\overline{\mathbb Q}_p$ agree, and such that for all $t\in\overline{\mathbb Q}$ one has $P$-valuation $<1$ iff $\|\iota t\|<1$, and $t\in P$ iff $\|\iota t\|\le 1$. Let $H$ be a $p$-divisible group over $O$ of height $h$: levels `H.level v` that are finite free cocommutative Hopf $O$-algebras of rank $p^{vh}$, with surjective transition coalgebra maps whose kernels are the $p^v$-torsion ideals. Then there is a $\mathbb Z_p$-linear isomorphism $\Theta$ from [`TateModule p (H.Points (AlgebraicClosure ℚ))`](def/EllipticCurve_TateModule.html#L15) to [`TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15) — here `Points L` is the direct limit over $v$ of the convolution groups of $O$-algebra maps `H.level v →ₐ L`, and the Tate module consists of sequences $(y_n)$ with $p^n y_n=0$ and $p\,y_{n+1}=y_n$ — with two properties. First, $\Theta$ is equivariant: for every $O$-algebra automorphism $\tau'$ of $\overline{\mathbb Q}$ and every $\mathcal O_K$-algebra automorphism $\tau_l$ of $\overline{\mathbb Q}_p$ with $\iota\circ\tau'=\tau_l\circ\iota$, one has $\Theta(\tau'\cdot y)=\tau_l\cdot\Theta(y)$ for the componentwise actions `H.tateModuleRep`. Second, $\Theta$ transports integrality: if $y$ is such that each component $y_n$ is the image under `H.pointsMkAdd` of some point $g\in$ `H.Point (AlgebraicClosure ℚ) w` satisfying $P$-valuation of $g(a)-\varepsilon(a)$ less than $1$ for every $a$ in `H.level w` ($\varepsilon$ the counit), then each component of $\Theta y$ is likewise the image of a point $g'$ of the base-changed group over $\overline{\mathbb Q}_p$ at some level $w$ with $\|g'(a)-\varepsilon(a)\|<1$ for all $a$ in the base-changed level.
--
--   This is the comparison between the Tate module of a $p$-divisible group over $O$ computed over $\overline{\mathbb Q}$ at the place determined by $P$ and the Tate module of its base change to the ring of integers of a finite extension $K/\mathbb Q_p$ computed over $\overline{\mathbb Q}_p$, together with the matching of Galois actions and of the notion of points congruent to the identity. It serves as the bridge from the local statements about $p$-divisible groups over $\mathcal O_K$ to their global form at an arbitrary place, and is used in the analysis of inertia acting on such Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] [Algebra O (PadicAlgCl.ringOfIntegers p K)]
    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (hι : ∀ x : O, ((algebraMap O (PadicAlgCl.ringOfIntegers p K) x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x))
    (hιP : ∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1)
    (hιP' : ∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1)
    {h : ℕ} (H : PDivisibleGroup O p h) :
    ∃ Θ : TateModule p (H.Points (AlgebraicClosure ℚ)) ≃ₗ[ℤ_[p]] TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)),
      (∀ (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) →
        ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
          Θ (H.tateModuleRep (AlgebraicClosure ℚ) τ' y) = (H.baseChange (PadicAlgCl.ringOfIntegers p K)).tateModuleRep (PadicAlgCl p) τl (Θ y)) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul g) =
        (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
        ∀ n : ℕ, ∃ (w : ℕ) (g : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Point (PadicAlgCl p) w),
          (H.baseChange (PadicAlgCl.ringOfIntegers p K)).pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
            ((Θ y : TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p))) : ℕ → (H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)) n ∧
          ∀ a : (H.baseChange (PadicAlgCl.ringOfIntegers p K)).level w, ‖PDivisibleGroup.Point.toAlgHom g a -
            algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) := by sorry
