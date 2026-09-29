-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/59bdf050-a7b7-5fb3-b342-35eff21229b2
-- title:
--   Inertia at p surjects onto ℤₚ^× via χₚ
-- statement:
--   Let $\overline{\mathbb{Q}}$ be the algebraic closure `AlgebraicClosure ℚ`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $p$ be a prime number, and assume `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$. Let $u$ be a unit of the ring $\mathbb{Z}_p$ of $p$-adic integers. Then there exists an element $\sigma$ of `A.inertiaSubgroupIn ℚ` — that is, of the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$ into the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms, of the inertia subgroup of $A$ over $\mathbb{Q}$ — such that the value of the $p$-adic cyclotomic character `cyclotomicCharacter (AlgebraicClosure ℚ) p` on the ring automorphism underlying $\sigma$ equals $u$. Thus the cyclotomic character restricted to the inertia group of any valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ is surjective onto $\mathbb{Z}_p^\times$; no injectivity or continuity assertion is made.
--
--   This is the total ramification of the cyclotomic tower $\mathbb{Q}(\zeta_{p^\infty})/\mathbb{Q}$ at $p$, packaged as surjectivity of $\chi_p$ on an inertia group, which is the form in which local reciprocity at $p$ is read off on inertia. It is used to produce inertia elements with prescribed cyclotomic character when analysing the action of inertia at $p$ on $p$-power torsion and on the eigenvalues attached to newforms; it is deduced from the corresponding statement at each finite level $p^k$ with values in $(\mathbb{Z}/p^k)^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq.lean

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} [Fact p.Prime] (hA : A.LiesOverPrime p)
    (u : ℤ_[p]ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ,
      cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv = u := by sorry
