-- Prove2me | Theorems.Thm_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
-- name    : ValuationSubring.exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/e8f701ac-b1af-5077-8537-d4fc6a3c401e
-- title:
--   Teichmüller lift of a finite-field embedding into mathcal O_P
-- statement:
--   Let $p$ be a prime and let $P$ be a valuation subring of $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbf Q}$ is a nonunit of $P$. Let $O$ be a commutative ring equipped with a ring homomorphism $i : O \to P$ that is injective and whose image covers the inertia invariants in the following sense: for every $y \in \overline{\mathbf Q}$ lying in $P$ and fixed by every $\sigma$ in `P.inertiaSubgroupIn ℚ` — the image in $\mathrm{Aut}(\overline{\mathbf Q}/\mathbf Q)$ of the inertia subgroup of $P$ over $\mathbf Q$ under the inclusion of the decomposition subgroup — there is $x \in O$ with $i(x) = y$ as elements of $\overline{\mathbf Q}$. Let $F$ be a finite field with $\mathrm{card}\,F = p^{s}$ for some natural number $s$. Then there exist a monoid homomorphism $\chi : F^{\times} \to O^{\times}$ and a ring homomorphism $\iota_0 : F \to \mathrm{ResidueField}(P)$ such that for every $l \in F^{\times}$ the residue of $i(\chi(l))$ in the residue field of $P$ equals $\iota_0(l)$. No injectivity of $\iota_0$ is asserted, although it is automatic for a ring homomorphism out of a field.
--
--   This is the Teichmüller (multiplicative) lift at a place of $\overline{\mathbf Q}$ above $p$, in a form where the coefficient ring $O$ is an abstract carrier mapping injectively onto the inertia-invariant part of the valuation ring: an embedding of a finite field $F$ into the residue field is lifted multiplicatively to characters $F^{\times} \to O^{\times}$. It is used in the construction of normal-form models of finite flat group schemes of type $(p,\dots,p)$ with simple inertia action, and in producing sections of Riemann–Roch spaces on modular curves with prescribed residues and inertia behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
    (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {O : Type*} [CommRing O] (i : O →+* ↥P) (hinj : Function.Injective i)
    (hO : ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
      ∃ x : O, ((i x : ↥P) : AlgebraicClosure ℚ) = y)
    (F : Type*) [Field F] [Fintype F] (s : ℕ) (hF : Fintype.card F = p ^ s) :
    ∃ (χ : Fˣ →* Oˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P),
      ∀ l : Fˣ, IsLocalRing.residue ↥P (i ((χ l : Oˣ) : O)) = ι₀ l := by sorry
