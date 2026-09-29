-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bd10e0a8-9cb4-5e23-b9cf-5a47c9ca7d5f
-- title:
--   Tame character attains a primitive m-th root of unity on inertia
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $p$ be a prime number, and assume `P.LiesOverPrime p`, i.e. that the image of $p$ in $\overline{\mathbb{Q}}$ lies in the non-units of $P$ (so $P$ is a place above $p$). Let $m$ be a natural number with $p \nmid m$ (which in particular forces $m \neq 0$), and let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^m = p$. The assertion is that there exists an element $\sigma$ of `P.inertiaSubgroupIn ℚ` — the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}\text{-alg}} \overline{\mathbb{Q}}$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$ — such that $\mathrm{tc}_\pi(\sigma) :=$ `P.tameCharacter π σ` is a primitive $m$-th root of unity in the residue field of $P$, i.e. its $m$-th power is $1$ and $m$ divides every exponent $l$ with $\mathrm{tc}_\pi(\sigma)^l = 1$. Here `P.tameCharacter π σ` is by definition the residue class of $\sigma\pi/\pi$ in the residue field of $P$ when $\sigma\pi/\pi$ lies in $P$, and $0$ otherwise.
--
--   This is the surjectivity of the tame character attached to an $m$-th root of $p$ onto the $m$-th roots of unity of the residue field (for $m = p^n - 1$, the surjectivity of Serre's fundamental character of level $n$ of tame inertia). It is used in the analysis of the restriction to inertia at $p$ of the mod $p$ representations attached to newforms, where the possible shapes of the inertial image are pinned down.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hP : P.LiesOverPrime p) {m : ℕ} (hpm : ¬ p ∣ m) {π : AlgebraicClosure ℚ} (hπ : π ^ m = p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, IsPrimitiveRoot (P.tameCharacter π σ) m := by sorry
