-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
-- name    : ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/5e8250a4-90d8-5319-a6ee-19298349a390
-- title:
--   Places of ℚ̄ above p are conjugate, compatibly with residue isomorphisms
-- statement:
--   Let $p$ be a natural number carrying a `Fact` instance that it is prime, and let $A$ and $A'$ be valuation subrings of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Assume the residue field $\kappa_A =$ `IsLocalRing.ResidueField A` has characteristic $p$, and let $e \colon \kappa_{A'} \xrightarrow{\ \sim\ } \kappa_A$ be an arbitrary ring isomorphism of the residue field of $A'$ onto that of $A$ (no compatibility with any base field is imposed on $e$). The conclusion asserts the existence of a $\mathbb{Q}$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}$ with two properties: first, $\tau \bullet A' = A$, where $\bullet$ is the pointwise action of the automorphism group on valuation subrings, so that $\tau$ carries the place $A'$ to the place $A$; and second, $\tau$ induces precisely $e$ on residue fields, in the form that for every $x \in A'$ and every $y \in A$ whose image in $\overline{\mathbb{Q}}$ equals $\tau(x)$, the residue of $y$ in $\kappa_A$ equals $e$ applied to the residue of $x$ in $\kappa_{A'}$.
--
--   This is the Galois theory of valuations for the infinite extension $\overline{\mathbb{Q}}/\mathbb{Q}$ in one package: $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acts transitively on the places above $p$, and the decomposition group of such a place maps onto the automorphism group of its residue field $\overline{\mathbb{F}}_p$. It is used to move a prescribed reduction of a Weierstrass curve to a chosen place above $p$, in [`WeierstrassCurve.exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius`](thm.html#WeierstrassCurve.exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius) and [`WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise in

theorem ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField (p : ℕ) [Fact p.Prime] (A A' : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) p] (e : IsLocalRing.ResidueField A' ≃+* IsLocalRing.ResidueField A) : ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ • A' = A ∧ ∀ (x : A') (y : A), (y : AlgebraicClosure ℚ) = τ (x : AlgebraicClosure ℚ) → IsLocalRing.residue A y = e (IsLocalRing.residue A' x) := by sorry
