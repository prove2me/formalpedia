-- Prove2me | Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
-- name    : ValuationSubring.residueField_charP_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/f01eb09c-7d12-55a8-99b9-f6d94dc72910
-- title:
--   Residue field of a valuation subring over ℓ has characteristic ℓ
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$, so that $A$ is a local ring with maximal ideal its set of nonunits. Let $\ell$ be a natural number, assumed prime, and suppose $A$ satisfies the project predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) for $\ell$, which by definition says that the image of $\ell$ under the canonical map $\mathbb{N} \to L$ lies in `A.nonunits`, i.e. the element $\ell$ of $L$ belongs to $A$ and is not a unit of $A$ — equivalently, $\ell$ lies in the maximal ideal $\mathfrak{m}_A$. The conclusion is that the residue field $\kappa(A) = A/\mathfrak{m}_A$, formed as `IsLocalRing.ResidueField A`, has characteristic $\ell$ in the sense of `CharP`: a natural number $n$ maps to $0$ in $\kappa(A)$ precisely when $\ell \mid n$. Thus a place of $L$ whose maximal ideal contains $\ell$ has residue characteristic $\ell$.
--
--   This is the elementary compatibility between a valuation of $L$ lying over the rational prime $\ell$ and the characteristic of its residue field; it lets residue fields at such places be treated as fields of characteristic $\ell$. It is used throughout the parts of the development that work with reduction of elliptic curves and with mod $\ell$ and mod $p$ coefficients at a place of residue characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_residueField_charP_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.residueField_charP_of_liesOverPrime {L : Type*} [Field L]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) :
    CharP (IsLocalRing.ResidueField A) ℓ := by sorry
