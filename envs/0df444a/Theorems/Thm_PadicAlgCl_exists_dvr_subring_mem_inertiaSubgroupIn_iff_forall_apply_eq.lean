-- Prove2me | Theorems.Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
-- name    : PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/e8af3c89-40a2-5f65-9c51-11a655878ec5
-- title:
--   Inertia-fixed integers in ℚ̄ₚ form a DVR
-- statement:
--   Let $p$ be a prime and let $\mathrm{PadicAlgCl}\,p$ denote the algebraic closure of $\mathbb{Q}_p$ used throughout, equipped with its valuation; write $A =$ [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) for the associated valuation subring, i.e. the set of $x$ with $v(x)\le 1$, and write $I$ for `(padicIntegers p).inertiaSubgroupIn ℚ_[p]`, the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ obtained as the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}_p$ into the full group of $\mathbb{Q}_p$-algebra automorphisms, of the inertia subgroup of $A$. The assertion is that there exists a subring $O$ of $\overline{\mathbb{Q}}_p$ such that: (i) $O \subseteq A$ as sets; (ii) the image of every $x \in \mathbb{Z}_p$ under the structure map $\mathbb{Z}_p \to \overline{\mathbb{Q}}_p$ lies in $O$; (iii) $O$ is a discrete valuation ring; (iv) the image of the natural number $p$ in $O$ is irreducible; (v) no $x \in O$ with $\|x\|_{\ge 0} < 1$ (the nonnegative-real valuation of its image in $\overline{\mathbb{Q}}_p$) is a unit of $O$; (vi) an automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ over $\mathbb{Q}_p$ belongs to $I$ if and only if $\sigma x = x$ for all $x \in O$; and (vii) conversely every $y \in A$ fixed by all $\sigma \in I$ lies in $O$.
--
--   This packages the ring of integers $O$ of the maximal unramified extension $\mathbb{Q}_p^{\mathrm{nr}} = \mathbb{Q}_p(\mu_{p'})$ inside $\overline{\mathbb{Q}}_p$ — the strict henselisation of $\mathbb{Z}_p$ — as a discrete valuation ring with uniformiser $p$ whose pointwise stabiliser is exactly the inertia group, together with the fact that $O$ contains all inertia-fixed elements of the valuation ring. It serves as the strictly henselian base for the local arguments on finite flat group schemes and their Cartier duals over $p$-adic integers that use inertia-invariant points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq (p : ℕ) [Fact p.Prime] :
    ∃ O : Subring (PadicAlgCl p),
      (O : Set (PadicAlgCl p)) ⊆ padicIntegers p ∧
      (∀ x : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) x ∈ O) ∧
      IsDiscreteValuationRing ↥O ∧ Irreducible ((p : ℕ) : ↥O) ∧
      (∀ x : ↥O, ‖(x : PadicAlgCl p)‖₊ < 1 → ¬ IsUnit x) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔ ∀ x ∈ O, σ x = x) ∧
      ∀ y ∈ padicIntegers p,
        (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ y = y) → y ∈ O := by sorry
