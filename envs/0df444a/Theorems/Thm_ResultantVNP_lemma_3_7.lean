-- Prove2me | Theorems.Thm_ResultantVNP_lemma_3_7
-- name    : ResultantVNP.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:39:50.55368+00:00
-- url     : https://prove2.me/theorems/03437fb6-50b2-47b8-9aa7-587acde876b8
-- title:
--   Lemma 3.7 — direct extraction of the grid assignment sum
-- statement:
--   Let $m=3^r+1$ with $r\ge1$, put $s=m^2$, and let $\kappa_{n,m}\ne0$ be the coefficient from Theorem 3.5 (the common coefficient in $\Phi_{n,s}$ of all assignment monomials). Then for every choice of nonempty disjoint index classes of total size $n$ and every symmetric tensor $A$ of dimension $n$ supported on the grid triangles,
--
--   $$
--   \Phi_{n,s}(A)=\kappa_{n,m}\,H_m(A).
--   $$
--
--   **Formalization Note** The identity is stated for tensors with entries in an arbitrary commutative ring; complex entries are the printed case, and the proof of Theorem 3.2 applies it to a tensor with polynomial entries.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - generalization: A a symmetric tensor with complex entries (Section 2.3) → A : Sym (Fin n) 3 → S for an arbitrary commutative ring S; reason: the identity is a polynomial identity; S = ℂ is the printed case and the proof of Theorem 3.2 uses polynomial entries
--   - encoding: κ_{n,m} ≠ 0 is the coefficient from Theorem 3.5 → a conjunct stating that κ is the common coefficient of every assignment monomial in Φ_{n,s}; reason: ties κ to Theorem 3.5 inside the statement
--   - encoding: nonempty pairwise disjoint index classes Ω_ij of total size n → fibres of a surjective cls : Fin n → ZMod m × ZMod m; reason: the same data
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.7, Eq. (7), p.17

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_SupportedOnGrid

namespace ResultantVNP

/-- **Lemma 3.7 (Direct extraction of the grid assignment sum).** Let `m = 3^r + 1` with `r ≥ 1`, put
`s = m²`, and let `A` be a symmetric tensor of dimension `n` supported on the grid triangles. Then
`Φ_{n,s}(A) = κ_{n,m} H_m(A)`, where `κ_{n,m} ≠ 0` is the coefficient from Theorem 3.5.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.7, Eq. (7), p.17.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. The first two conjuncts identify `κ` as the common nonzero coefficient of the assignment monomials
in `Φ_{n,s}` (Theorem 3.5). The identity is stated for tensors with entries in an arbitrary commutative
ring `S` (`Φ_{n,s}(A)` is `aeval A`); `S = ℂ` is the printed case, and the proof of Theorem 3.2 applies it
to a tensor with polynomial entries. Index classes are the fibres of a surjective `cls`. -/
theorem lemma_3_7 (𝓡 : ResultantSystem) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    ∃ κ : ℤ, κ ≠ 0 ∧
      (∀ cls : Fin n → ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1), Function.Surjective cls →
        ∀ ν : (∀ p, {α // cls α = p}),
          (charCoeff 𝓡 n ((3 ^ r + 1) ^ 2)).coeff (assignMonomial cls ν) = κ) ∧
      ∀ cls : Fin n → ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1), Function.Surjective cls →
        ∀ (S : Type) [CommRing S] (A : Sym (Fin n) 3 → S), SupportedOnGrid cls A →
          MvPolynomial.aeval A (charCoeff 𝓡 n ((3 ^ r + 1) ^ 2)) = (κ : S) * gridSum cls A := by sorry

end ResultantVNP
