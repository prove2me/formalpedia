-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/d981d918-ea05-5fda-aac5-f2755f5e5ec3
-- title:
--   Mod p cyclotomic character surjects onto inertia at p
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the Lean algebraic closure `AlgebraicClosure ℚ`), let $p$ be a prime number, and assume `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (equivalently, $p$ lies in the maximal ideal of $A$, so the place determined by $A$ lies above $p$). Let $a$ be a unit of $\mathbb{Z}/p\mathbb{Z}$. The assertion is that there exists an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lying in `A.inertiaSubgroupIn ℚ` — the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$ into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, of the inertia subgroup of $A$ over $\mathbb{Q}$ — such that for every $\mu \in \overline{\mathbb{Q}}$ with $\mu^p = 1$ one has $\sigma(\mu) = \mu^{n}$, where $n$ is the canonical representative in $\{0,\dots,p-1\}$ of the underlying element of $\mathbb{Z}/p\mathbb{Z}$ of $a$. Thus every prescribed value in $(\mathbb{Z}/p\mathbb{Z})^{\times}$ is attained by the action on the $p$-th roots of unity by some element of the inertia group at the chosen place above $p$.
--
--   This is the surjectivity of the mod $p$ cyclotomic character on an inertia subgroup at $p$, $\bar\chi_p(I_p) = \mathbb{F}_p^{\times}$, reflecting the total ramification of $\mathbb{Q}(\zeta_p)/\mathbb{Q}$ at $p$. It is the input for the statement that the determinant of the mod $p$ Galois representation attached to an elliptic curve is onto on inertia above $p$, and is used wherever this surjectivity of the cyclotomic character on inertia is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.lean

import Mathlib.Data.ZMod.Basic
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ (a : ZMod p).val := by sorry
