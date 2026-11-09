-- Prove2me | Theorems.Thm_ResultantVNP_theorem_3_2
-- name    : ResultantVNP.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:31.195206+00:00
-- url     : https://prove2.me/theorems/f8804c5a-e399-45e7-8013-314b32c209cb
-- title:
--   Theorem 3.2 — VNP-hardness of $\{\Phi_{5m^2,m^2}\}_{m\ge3}$ under p-projections
-- statement:
--   The family $\{\Phi_{5m^2,m^2}\}_{m\ge3}$ on symmetric cubic tensors, with one independent variable for each unordered triple of indices, is VNP-hard under p-projections over $\mathbb C$. The projections from the permanent use only rational constants: there is a polynomially bounded $t$ with $t(n)\ge3$ such that for every $n\ge1$ the permanent of the generic $n\times n$ matrix is a projection of $\Phi_{5t(n)^2,t(n)^2}$ in which every substituted constant is rational.
--
--   Theorem 1.4 follows from this by homogenization.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: the family indexed by m ≥ 3 → family given for every m, with the p-projection index t(n) required to be ≥ 3; reason: only members with m ≥ 3 are used
--   - reading: the projections from the permanent use only rational constants → ∃ t polynomially bounded, ∀ n ≥ 1, t n ≥ 3 and per_n (generic n × n matrix over ℂ) is a projection of Φ_{5t(n)², t(n)²} with every substituted constant in ℚ; reason: the permanent family p-projects to the coefficient family with rational constants, as the proof gives (Z' = diag(Z, κ⁻¹))
--   - encoding: Φ_{n,s} over ℤ; VNP over ℂ → Φ mapped to ℂ by Int.castRingHom; reason: Lean convention; same polynomial
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 3.2, p.14 (proof p.17)

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_IsVNPHardPProj

namespace ResultantVNP

/-- **Theorem 3.2.** The family `{Φ_{5m²,m²}}_{m≥3}` on symmetric cubic tensors, with one independent
variable for each unordered triple of indices, is VNP-hard under p-projections over `ℂ`. The
projections from the permanent use only rational constants.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 3.2, p.14 (proof p.17).

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `Φ` is mapped from `ℤ` to `ℂ`. The index set `{m ≥ 3}` is the bound `3 ≤ t(n)` on the indices used.
The second sentence is read as: the permanent family `per_n` (`n ≥ 1`, generic `n × n` matrix) is a
p-projection of `{Φ_{5m²,m²}}_{m≥3}` in which every substituted constant is rational. -/
theorem theorem_3_2 (𝓡 : ResultantSystem) :
    IsVNPHardPProj
        (fun m => MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * m ^ 2) (m ^ 2))) 3 ∧
      ∃ t : ℕ → ℕ, PolyBounded t ∧ ∀ n, 1 ≤ n → 3 ≤ t n ∧
        ∃ ρ : Sym (Fin (5 * t n ^ 2)) 3 → (Fin n × Fin n) ⊕ ℚ,
          MvPolynomial.aeval
              (fun T => Sum.elim MvPolynomial.X (fun q : ℚ => MvPolynomial.C (q : ℂ)) (ρ T))
              (MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * t n ^ 2) (t n ^ 2))) =
            (Matrix.of fun i j : Fin n =>
              (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent := by sorry

end ResultantVNP
