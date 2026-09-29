-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
-- name    : ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b14e8512-ba6d-5458-8597-2c18ce9da5a5
-- title:
--   A p-adically complete target for all local evaluations into A
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ such that $A$ lies over $p$, i.e. the image of $p$ lies in $A.\mathrm{nonunits}$, equivalently $A.\mathrm{valuation}(p) < 1$. The assertion is that there exist a type $S$ (in the lowest universe) carrying a commutative ring structure and a ring homomorphism $j_A \colon A \to S$ with the following two properties. First, unit descent: for all $\alpha, \beta \in A$ and every unit $u \in S^{\times}$ with $j_A(\alpha) = j_A(\beta)\,u$, there is a unit $v \in A^{\times}$ with $\alpha = \beta v$. Second, universal completed evaluation: for every type $B$ (again in the lowest universe) equipped with a commutative ring structure which is Noetherian and local, and every ring homomorphism $\chi \colon B \to A$ that is a local homomorphism, there exists a ring homomorphism $\psi$ from the $\mathfrak{m}_B$-adic completion $\mathrm{AdicCompletion}(\mathfrak{m}_B, B)$ to $S$ such that the composite of the canonical map $B \to \mathrm{AdicCompletion}(\mathfrak{m}_B, B)$ with $\psi$ equals $\chi$ followed by $j_A$. Note that $S$ and $j_A$ are produced once and for all, before the quantification over $B$ and $\chi$.
--
--   This provides a single $p$-adically complete receptacle, together with a map from the valuation ring $A$, through which every evaluation at $A$-points of a Noetherian local ring factors after completion, while units in the receptacle detect only units of $A$. It is used in the analysis of local models of the modular curve at $p$, where sections and charts must be evaluated on the completed local rings and unit ambiguities pushed back to $A^{\times}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (S : Type) (_ : CommRing S) (jA : ↥A →+* S),
      (∀ (α β : ↥A) (u : Sˣ), jA α = jA β * (u : S) → ∃ v : (↥A)ˣ, α = β * (v : ↥A)) ∧
      ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (χ : B →+* ↥A), IsLocalHom χ →
        ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* S,
          ψ.comp (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) = jA.comp χ := by sorry
