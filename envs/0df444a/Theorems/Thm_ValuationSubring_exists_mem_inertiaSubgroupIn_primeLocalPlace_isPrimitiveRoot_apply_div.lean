-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bc953a7e-f718-50eb-9973-64ab3863fded
-- title:
--   Inertia at q moves √[m]q by a primitive root
-- statement:
--   Let $q$ be a prime number and $m$ a natural number with $q \nmid m$, and let $\alpha \in \overline{\mathbb{Q}}$ (the algebraic closure `AlgebraicClosure ℚ`) satisfy $\alpha^m = q$, the image of $q$ under the natural map $\mathbb{N} \to \overline{\mathbb{Q}}$. Write $P =$ `primeLocalPlace q` for the valuation subring of $\overline{\mathbb{Q}}$ obtained by pulling back the ring of $q$-adic integers along the chosen embedding [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) of $\overline{\mathbb{Q}}$ into an algebraic closure of $\mathbb{Q}_q$, and let `(primeLocalPlace q).inertiaSubgroupIn ℚ` be the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $P$ into the full automorphism group. The assertion is that there exists $\sigma$ in this inertia subgroup such that $\sigma(\alpha)/\alpha$ is a primitive $m$-th root of unity in $\overline{\mathbb{Q}}$, in the sense of Mathlib's `IsPrimitiveRoot`. Note that $m = 0$ is excluded automatically: $\alpha^0 = 1 \neq q$.
--
--   This is the tame Kummer computation at the prime $q$ itself: the inertia group at a place above $q$ acts on an $m$-th root of $q$ through the full group of $m$-th roots of unity when $q \nmid m$, the hypothesis $q \nmid m$ excluding the wild case. It serves as the statement at the distinguished place `primeLocalPlace q`, from which [`ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter) transports the conclusion, and it supplies the surjectivity of the tame character used in the local analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div
    (q : Nat.Primes) {m : ℕ}
    (hqm : ¬ (q : ℕ) ∣ m) {α : AlgebraicClosure ℚ} (hα : α ^ m = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ σ ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ, IsPrimitiveRoot (σ α / α) m := by sorry
