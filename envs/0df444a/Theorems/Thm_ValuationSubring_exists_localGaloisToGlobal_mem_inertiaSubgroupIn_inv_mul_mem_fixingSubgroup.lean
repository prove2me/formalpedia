-- Prove2me | Theorems.Thm_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
-- name    : ValuationSubring.exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/1de38be9-4302-5b6d-b37c-61a464a355b5
-- title:
--   Local inertia approximates global inertia at finite level
-- statement:
--   Let $p$ be a prime. Write $\iota_p\colon \overline{\mathbb Q}\to \overline{\mathbb Q}_p$ for the algebra embedding [`padicEmbedding p`](def/GaloisRep_CompletionBridge.html#L17) of $\overline{\mathbb Q}$ into the algebraic closure `PadicAlgCl p` of $\mathbb Q_p$ obtained by lifting along algebraic closedness, and let [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) be the valuation subring of $\overline{\mathbb Q}$ pulled back along $\iota_p$ from the valuation subring of the canonical valuation on `PadicAlgCl p`. For a valuation subring $A$ of $L/K$, the group $A.\mathrm{inertiaSubgroupIn}\,K$ is the image in $L\simeq_{\mathrm{alg}[K]}L$ of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup. Let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lying in the inertia subgroup of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is finite-dimensional over $\mathbb Q$. Then there exists a $\mathbb Q_p$-algebra automorphism $\tau$ of `PadicAlgCl p` such that its image $r_p(\tau)$ under [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) — restriction of scalars to $\mathbb Q$ followed by `AlgEquiv.restrictNormalHom` to $\overline{\mathbb Q}$ — again lies in the inertia subgroup of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25), and such that $\sigma^{-1}\cdot r_p(\tau)$ lies in the fixing subgroup of $F$, i.e. $r_p(\tau)$ agrees with $\sigma$ on $F$.
--
--   This is the inertia analogue, in finite-level (approximation) form, of the statement that the decomposition group of the $p$-adic place of $\overline{\mathbb Q}$ is contained in the closure of the image of $\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$: every global inertia element at $p$ is matched, on any prescribed finite subextension $F/\mathbb Q$, by an element coming from the local Galois group and still lying in inertia. It is used in the analysis of the action of inertia at $p$ on torsion points, through [`ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp`](thm.html#ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
    (p : ℕ) [Fact p.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ (padicPlace p).inertiaSubgroupIn ℚ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ ∧
        σ⁻¹ * localGaloisToGlobal p τ ∈ F.fixingSubgroup := by sorry
