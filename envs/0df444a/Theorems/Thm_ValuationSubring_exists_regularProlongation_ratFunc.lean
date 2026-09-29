-- Prove2me | Theorems.Thm_ValuationSubring_exists_regularProlongation_ratFunc
-- name    : ValuationSubring.exists_regularProlongation_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/a09f1166-bca3-591d-abdd-97782f4e0801
-- title:
--   Existence of the Gauss prolongation to L(X)
-- statement:
--   Let $L$ be a field and let $A \subseteq L$ be a valuation subring, with residue field $k = \mathrm{ResidueField}\,A$, the quotient of $A$ by its maximal ideal. The assertion is that there exists a `RegularProlongation` of $A$ along the field extension $L \subseteq \mathrm{RatFunc}\,L = L(X)$ with residue field $\mathrm{RatFunc}\,k = k(X)$, that is: a valuation subring $\mathcal{O}$ of $L(X)$ together with a ring homomorphism $\rho \colon \mathcal{O} \to k(X)$ such that an element $x \in L$ lies in $\mathcal{O}$ (under the structure map $L \to L(X)$) exactly when $x \in A$; $\rho$ is surjective; the kernel of $\rho$ is the maximal ideal of $\mathcal{O}$; $\rho$ restricted to $A$ agrees with the reduction $A \to k$ followed by $k \to k(X)$; and every nonzero $f \in L(X)$ admits a scalar $c \in L$ with $c \cdot f \in \mathcal{O}$ and $\rho(c \cdot f) \neq 0$ (so the value group of $\mathcal{O}$ is that of $A$). Moreover this prolongation is normalised: $X \in \mathcal{O}$ with $\rho(X) = X$, and for every polynomial $p \in A[X]$, the image of $p$ in $L(X)$ (coefficients mapped into $L$) lies in $\mathcal{O}$ and $\rho$ sends it to the image in $k(X)$ of the polynomial obtained from $p$ by reducing its coefficients modulo the maximal ideal of $A$.
--
--   This is the Gauss (inf) extension of a valuation to a rational function field in one variable, packaged as a regular prolongation with the normalisations that pin down the residue extension as $k \subseteq k(X)$ with $X$ mapping to $X$. It serves as the base case for producing regular prolongations along transcendental extensions, and is used in the analysis of prolongations over algebraically closed residue fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_regularProlongation_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_regularProlongation_ratFunc
    {L : Type*} [Field L] (A : ValuationSubring L) :
    ∃ R : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)),
      (∃ hX : (RatFunc.X : RatFunc L) ∈ R.integers,
        R.residue ⟨RatFunc.X, hX⟩ = RatFunc.X) ∧
      (∀ p : Polynomial A, ∃ hp : algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype) ∈ R.integers,
        R.residue ⟨algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype), hp⟩ =
          algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
            (p.map (IsLocalRing.residue A))) := by sorry
