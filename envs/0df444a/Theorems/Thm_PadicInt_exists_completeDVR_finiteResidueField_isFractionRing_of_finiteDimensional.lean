-- Prove2me | Theorems.Thm_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
-- name    : PadicInt.exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/cb5cb45a-1805-5380-a223-17d019e18dff
-- title:
--   Ring of integers of a finite extension of ℚₚ
-- statement:
--   Let $p$ be a prime and let $K$ be a field equipped with a $\mathbb{Q}_p$-algebra structure making it finite-dimensional over $\mathbb{Q}_p$. The assertion is that there exists a type $\mathcal{O}$ carrying a commutative ring structure which is a domain, a discrete valuation ring, adically complete with respect to its maximal ideal, with finite residue field, of characteristic zero, together with a $\mathbb{Z}_p$-algebra structure on $\mathcal{O}$, an $\mathcal{O}$-algebra structure on $K$ exhibiting $K$ as a fraction field of $\mathcal{O}$, and such that three further conditions hold: (i) for every $z \in \mathbb{Z}_p$ the image of $z$ in $K$ along $\mathbb{Z}_p \to \mathcal{O} \to K$ agrees with the image of $z$ under $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p \to K$, so the two routes from $\mathbb{Z}_p$ into $K$ coincide; (ii) an element $x \in K$ lies in the image of the structure map $\mathcal{O} \to K$ if and only if $x$ is integral over $\mathbb{Z}_p$ with respect to the composite ring homomorphism $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p \to K$, i.e. satisfies a monic polynomial with coefficients in the image of $\mathbb{Z}_p$; and (iii) the image of $p$ in $\mathcal{O}$ lies in the maximal ideal of $\mathcal{O}$.
--
--   This is the standard structure theory of the ring of integers $\mathcal{O}$ of a $p$-adic local field $K$, packaged as an existential bundle of instances on a carrier type so that results stated over "a complete discrete valuation ring of characteristic zero with finite residue field and fraction field $K$" can be instantiated at the coefficient field of a $p$-adic Galois representation. It is used in the analysis of the rational Tate module via an inertia-fixed eigenplane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : Finite (IsLocalRing.ResidueField O))
      (_ : CharZero O) (_ : Algebra ℤ_[p] O) (_ : Algebra O K) (_ : IsFractionRing O K),
      (∀ z : ℤ_[p], algebraMap O K (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] K (z : ℚ_[p])) ∧
      (∀ x : K, (∃ o : O, algebraMap O K o = x) ↔
        RingHom.IsIntegralElem ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) x) ∧
      ((p : O) ∈ IsLocalRing.maximalIdeal O) := by sorry
