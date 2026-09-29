-- Prove2me | Theorems.Thm_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
-- name    : ValuationSubring.exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/deacdbe6-f4a1-5a5c-9965-e063098ed153
-- title:
--   Étale ℤ-algebra neighbourhoods exhaust the decomposition ring
-- statement:
--   Let $p$ be a prime and let $Pl$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose associated maximal ideal contains $p$, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $Pl$ (this is the meaning of `Pl.LiesOverPrime p`). Let $x \in \overline{\mathbb{Q}}$ lie in the intersection, taken inside the subring lattice of $\overline{\mathbb{Q}}$, of $Pl$ with the fixed field of the decomposition subgroup of $Pl$ over $\mathbb{Q}$, that is, $x$ lies in $Pl$ and is fixed by every element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ preserving $Pl$. Then there exist a commutative ring $E$ in the lowest universe that is étale as a $\mathbb{Z}$-algebra, a ring homomorphism $\iota : E \to \overline{\mathbb{Q}}$ and a ring homomorphism $\varphi_0 : E \to \mathbb{Z}/p$ such that: $\iota(e) \in Pl$ for every $e \in E$; for all $e \in E$ and all $n \in \mathbb{Z}$ with $n \bmod p = \varphi_0(e)$ one has $Pl.\mathrm{valuation}(\iota(e) - n) < 1$; and $x$ belongs to the range of $\iota$. No surjectivity of $\varphi_0$ or injectivity of $\iota$ is asserted.
--
--   This is the statement that the decomposition ring of a place of $\overline{\mathbb{Q}}$ above $p$ — the intersection of the valuation ring with the decomposition field — is exhausted by the images of étale $\mathbb{Z}$-algebras admitting a residue map to the prime field $\mathbb{Z}/p$ compatible with the valuation, one half of the identification of that ring with the henselisation of $\mathbb{Z}_{(p)}$. It is used in [`ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing`](thm.html#ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing), and rests on the discrete valuation ring and Henselian local ring properties of the decomposition ring together with its residue map to $\mathbb{Z}/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (x : AlgebraicClosure ℚ)
    (hx : x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra.Etale ℤ E) (ι : E →+* AlgebraicClosure ℚ) (φ₀ : E →+* ZMod p),
      (∀ e : E, ι e ∈ Pl) ∧
      (∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) ∧
      x ∈ Set.range ι := by sorry
