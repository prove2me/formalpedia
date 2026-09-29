-- Prove2me | Theorems.Thm_TaylorWiles_exists_isTaylorWilesPrime
-- name    : TaylorWiles.exists_isTaylorWilesPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/5bab3426-5b88-55b3-88b9-0c4d422c0b33
-- title:
--   Existence of Taylor–Wiles primes avoiding a finite set
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$, let $\mathbb{k}$ be a field, and let $\rho$ be a monoid homomorphism from $\mathrm{Gal}(L/\mathbb{Q}) = L \simeq_{\mathbb{Q}} L$ to the $2 \times 2$ matrices over $\mathbb{k}$ (the project's notion `ResidualRep`). Fix natural numbers $p$ and $n$, a finite set $S$ of natural numbers, and a `Seed` for $\rho$, $p$, $n$, $S$: that is, an element $\sigma \in \mathrm{Gal}(L/\mathbb{Q})$ such that $\rho(\sigma)$ has distinct rational eigenvalues, meaning there are $\alpha \neq \beta$ in $\mathbb{k}$ with $\operatorname{tr}\rho(\sigma) = \alpha + \beta$ and $\det\rho(\sigma) = \alpha\beta$, together with the condition that every $\ell \notin S$ which is realised cyclically by $\sigma$ satisfies $\ell \equiv 1 \pmod{p^n}$; here $\ell$ is realised cyclically when $\ell$ is prime and, for every prime ideal $Q$ of $\mathcal{O}_L$ lying over the ideal $(\ell)$ of $\mathbb{Z}$ with finite residue ring, some power $\sigma^k$ with $k$ coprime to the order of $\sigma$ is conjugate to the arithmetic Frobenius at $Q$. Then for any further finite set $T$ of natural numbers there is a natural number $q$ with $q \notin S$, $q \notin T$, such that $q$ is prime, $q \equiv 1 \pmod{p^n}$, and for every prime ideal $Q$ of $\mathcal{O}_L$ lying over $(q)$ with finite residue ring, $\rho$ of the arithmetic Frobenius at $Q$ has distinct rational eigenvalues in the above sense.
--
--   This is the unconditional supply of Taylor–Wiles auxiliary primes: from a single regular element $\sigma$ whose cyclic realisations outside $S$ are all $\equiv 1 \pmod{p^n}$, infinitely many (in particular, one outside any prescribed finite set) primes $q \equiv 1 \pmod{p^n}$ are produced at which $\rho(\mathrm{Frob}_q)$ has distinct eigenvalues in $\mathbb{k}$. It is invoked by [`ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed`](thm.html#ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_seed), the selection step that assembles the Taylor–Wiles sets of auxiliary primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TaylorWiles_exists_isTaylorWilesPrime.lean

import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField FrobeniusDensity

theorem TaylorWiles.exists_isTaylorWilesPrime
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q := by sorry
