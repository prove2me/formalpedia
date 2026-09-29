-- Prove2me | Theorems.Thm_ValuationSubring_localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace
-- name    : ValuationSubring.localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/170c6b29-f03c-58f0-bd19-bfe920f0b3a1
-- title:
--   Local inertia maps into inertia at the p-adic place
-- statement:
--   Let $p$ be a natural number assumed prime. Write $\mathrm{PadicAlgCl}\ p$ for the fixed algebraic closure of $\mathbb{Q}_p$, and let $\mathrm{padicIntegers}\ p$ be its valuation subring, namely the valuation subring attached to the canonical $\mathbb{R}_{\ge 0}$-valued valuation on $\mathrm{PadicAlgCl}\ p$. Let $\mathrm{padicEmbedding}\ p : \mathrm{AlgebraicClosure}\ \mathbb{Q} \to \mathrm{PadicAlgCl}\ p$ be the $\mathbb{Q}$-algebra embedding obtained by lifting along algebraic closedness, and let $\mathrm{padicPlace}\ p$ be the valuation subring of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ obtained by pulling back $\mathrm{padicIntegers}\ p$ along this embedding. Let $\mathrm{localGaloisToGlobal}\ p$ be the monoid homomorphism from $\mathbb{Q}_p$-algebra automorphisms of $\mathrm{PadicAlgCl}\ p$ to $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ given by restricting scalars to $\mathbb{Q}$ and then restricting the resulting automorphism to the normal subextension $\mathrm{AlgebraicClosure}\ \mathbb{Q}$. The assertion is: for every $\tau$ a $\mathbb{Q}_p$-algebra automorphism of $\mathrm{PadicAlgCl}\ p$ lying in $(\mathrm{padicIntegers}\ p).\mathrm{inertiaSubgroupIn}\ \mathbb{Q}_p$ — that is, in the image of the inertia subgroup of the decomposition subgroup under the inclusion of that decomposition subgroup into the full automorphism group — the image $\mathrm{localGaloisToGlobal}\ p\ \tau$ lies in $(\mathrm{padicPlace}\ p).\mathrm{inertiaSubgroupIn}\ \mathbb{Q}$, the corresponding image of the inertia subgroup at the place $\mathrm{padicPlace}\ p$ inside $\mathrm{Gal}(\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q})$.
--
--   This is the compatibility of inertia under the identification of the local Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ with the decomposition group at the chosen place of $\overline{\mathbb{Q}}$ above $p$: restriction carries local inertia into the global inertia group at that place. It is used in the passage between local and global ramification data, in particular in the analysis of roots of unity and $p$-power torsion under inertia and in the construction of ring homomorphisms from intermediate fields into $\overline{\mathbb{Q}}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace (p : ℕ) [Fact p.Prime]
    (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ := by sorry
