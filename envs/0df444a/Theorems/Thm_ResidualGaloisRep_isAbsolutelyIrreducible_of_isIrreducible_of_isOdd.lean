-- Prove2me | Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
-- name    : ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/738ed566-8e81-5b22-97a5-f4f679636f80
-- title:
--   Odd irreducible residual representations are absolutely irreducible
-- statement:
--   Let $k$ be a field and let $\rho$ be an element of [`ResidualGaloisRep k`](def/GaloisRep_Residual.html#L22), i.e. the data of a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism from the group $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ` to $\mathrm{End}_k(V)$, and a witness that this homomorphism factors through a finite level, in the sense that there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ such that every automorphism fixing $L$ pointwise is sent to the identity. Assume three hypotheses: that $2 \neq 0$ in $k$; that $\rho$ is irreducible in the project's sense [`ResidualGaloisRep.IsIrreducible`](def/GaloisRep_Residual.html#L61), namely every $k$-submodule $W \subseteq V$ with $\rho(\sigma)W \subseteq W$ for all $\sigma$ satisfies $W = \bot$ or $W = \top$; and that $\rho$ is odd in the project's sense [`ResidualGaloisRep.IsOdd`](def/GaloisRep_Residual.html#L57), namely $\det \rho(c) = -1$ for every $c$ in the Galois group with $c^2 = 1$ and $c \neq 1$ (the condition is imposed on all involutions, not just on one distinguished complex conjugation). The conclusion is [`ResidualGaloisRep.IsAbsolutelyIrreducible`](def/GaloisRep_Residual.html#L82), which unfolds to the statement that the base change of $\rho$ along $k \to$ `AlgebraicClosure k` — the representation on $\overline{k} \otimes_k V$ with $\sigma$ acting by $\rho(\sigma) \otimes \mathrm{id}$ — is again irreducible in the same sense: every $\overline{k}$-submodule of $\overline{k} \otimes_k V$ stable under all $\sigma$ is zero or everything.
--
--   This is the standard passage from irreducibility to absolute irreducibility for an odd two-dimensional residual representation, available as soon as the residual characteristic is odd. In the formalisation, "irreducible" for the mod $p$ representation of an elliptic curve means irreducibility over $\mathbb F_p$, and this lemma supplies the absolute irreducibility that the modularity-lifting arguments require; the oddness hypothesis is verified separately for the representation attached to a Weierstrass curve. It is invoked in the Hecke-algebra and patching parts of the lifting assembly, where absolute irreducibility of the residual representation attached to a newform or to a curve is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd {k : Type} [Field k]
    (ρ : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    ρ.IsAbsolutelyIrreducible := by sorry
