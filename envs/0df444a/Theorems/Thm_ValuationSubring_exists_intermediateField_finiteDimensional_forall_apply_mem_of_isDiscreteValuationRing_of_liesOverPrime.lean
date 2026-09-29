-- Prove2me | Theorems.Thm_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
-- name    : ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/a56c6e3d-7a15-5afc-93e4-e13d24b0aca8
-- title:
--   Finite extension of ℚₚ containing ι(R_h)
-- statement:
--   Let $p$ be a prime and let $Pl$ be a valuation subring of $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ` such that the image of $p$ in $\overline{\mathbf Q}$ is a nonunit of $Pl$ (this is the meaning of `Pl.LiesOverPrime p`). Let $R_h$ be a commutative domain that is a henselian local ring and a discrete valuation ring, equipped with an algebra structure over $\overline{\mathbf Q}$ whose structure map is injective (faithful scalar action), and assume: the image of every $x \in R_h$ in $\overline{\mathbf Q}$ lies in $Pl$; for every $x \in R_h$, membership of $x$ in the maximal ideal of $R_h$ is equivalent to $v_{Pl}(\mathrm{alg}(x)) < 1$ for the valuation attached to $Pl$; and $R_h$ carries an algebra structure over $\mathbf{Z}/p$ for which $x$ maps to $0$ exactly when $v_{Pl}(\mathrm{alg}(x)) < 1$. Let $\iota \colon \overline{\mathbf Q} \to$ `PadicAlgCl p` be a ring homomorphism such that $t \in Pl$ holds if and only if $\|\iota t\| \le 1$. Then there exists an intermediate field $K'$ of `PadicAlgCl p` over $\mathbf{Q}_p$ which is finite-dimensional over $\mathbf{Q}_p$ and satisfies $\iota(\mathrm{alg}(x)) \in K'$ for every $x \in R_h$.
--
--   The statement says that a henselian discrete valuation subring of $\overline{\mathbf Q}$ centred on a place above $p$ with residue field $\mathbf F_p$ is carried by an embedding inducing that place into a finite extension of $\mathbf Q_p$; the degree bound comes from the fact that the residue degree is $1$ and the ramification is bounded by the value of $p$ in $R_h$. It is used in the construction of the family of bialgebra homomorphisms attached to a $p$-divisible group from Galois-equivariant, level-preserving homomorphisms on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K' ∧ ∀ x : Rh, ι (algebraMap Rh (AlgebraicClosure ℚ) x) ∈ K' := by sorry
