-- Prove2me | Theorems.Thm_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues
-- name    : TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/fafbadc4-e78d-56e6-98e3-c7dda3a0ca09
-- title:
--   Seed element in the kernel of the cyclotomic character
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$, let $\mathbb{k}$ be a field, let $p$ be a prime with $p \neq 2$, and let $n$ be a natural number. Let $\rho \colon \mathrm{Gal}(L/\mathbb{Q}) = (L \simeq_{\mathbb{Q}} L) \to M_2(\mathbb{k})$ be a monoid homomorphism (the project's notion of a `ResidualRep`), and let $\zeta \in \mathcal{O}_L$ be a primitive $p^n$-th root of unity. Assume that $2 \neq 0$ in $\mathbb{k}$; that the $\mathbb{k}$-span of the set of matrices $\rho(g)$, $g \in \mathrm{Gal}(L/\mathbb{Q})$, is all of $M_2(\mathbb{k})$ (absolute irreducibility in Burnside's form); and that every $\rho(g)$ has its characteristic polynomial split over $\mathbb{k}$, in the sense that for each $g$ there are $a, b \in \mathbb{k}$ with $\operatorname{tr} \rho(g) = a + b$ and $\det \rho(g) = ab$. Then there is an element $\sigma$ in the kernel of the cyclotomic character $\mathrm{Gal}(L/\mathbb{Q}) \to (\mathbb{Z}/p^n)^{\times}$ attached to $\zeta$ (the map sending $g$ to the exponent of $g$ on $p^n$-th roots of unity, via `IsPrimitiveRoot.autToPow`) such that $\rho(\sigma)$ has distinct rational eigenvalues in the project's sense: there exist $\alpha \neq \beta$ in $\mathbb{k}$ with $\operatorname{tr} \rho(\sigma) = \alpha + \beta$ and $\det \rho(\sigma) = \alpha\beta$.
--
--   This is the seed step of the Taylor–Wiles prime selection: it produces the single Galois element, trivial on the $p^n$-th roots of unity and with regular semisimple image, whose Frobenius conjugates supply Taylor–Wiles primes $q \equiv 1 \pmod{p^n}$. It is used in [`ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible`](thm.html#ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues.lean

import Mathlib
import Definitions.Def_TaylorWiles_CyclotomicChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (ρ : TaylorWiles.ResidualRep L 𝕜) (n : ℕ)
    {ζ : 𝓞 L} [NeZero (p ^ n)] (hζ : IsPrimitiveRoot ζ (p ^ n))
    (h2 : (2 : 𝕜) ≠ 0)
    (hirr : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (hsplit : ∀ g : L ≃ₐ[ℚ] L, ∃ a b : 𝕜, (ρ g).trace = a + b ∧ (ρ g).det = a * b) :
    ∃ σ ∈ (TaylorWiles.cycloChar hζ).ker, (ρ σ).HasDistinctRationalEigenvalues := by sorry
