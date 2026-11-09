-- Prove2me | Theorems.Thm_ResultantVNP_theorem_3_5
-- name    : ResultantVNP.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:39:55.661188+00:00
-- url     : https://prove2.me/theorems/af3ffde0-4836-44a4-9d93-c7d7b45bdf17
-- title:
--   Theorem 3.5 — nonvanishing of assignment coefficients
-- statement:
--   Let $m\ge3$, put $s=m^2$, and let the index classes defining $H_m$ have total size $n$. Every monomial of $H_m$ has the same coefficient $\kappa_{n,m}\in\mathbb Z\setminus\{0\}$ in $\Phi_{n,s}$. This coefficient depends only on $n$ and $m$: one $\kappa_{n,m}\neq0$ serves for every choice of nonempty disjoint classes $\Omega_{ij}$ of total size $n$ and every assignment.
--
--   The constant $\kappa_{n,m}$ is the factor in Lemma 3.7 and the scaling inverted in the proof of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: nonempty pairwise disjoint index classes Ω_ij of total size n → fibres of a surjective cls : Fin n → ZMod m × ZMod m; reason: the same data
--   - reading: this coefficient depends only on n and m → κ is chosen before the class map and the assignment (∃ κ ≠ 0, ∀ cls surjective, ∀ ν); reason: the clause asserts independence of the classes and the monomial
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 3.5, p.15

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_gridSum

namespace ResultantVNP

/-- **Theorem 3.5 (Nonvanishing of assignment coefficients).** Let `m ≥ 3`, put `s = m²`, and let the
index classes defining `H_m` have total size `n`. Every monomial of `H_m` has the same coefficient
`κ_{n,m} ∈ ℤ \ {0}` in `Φ_{n,s}`. This coefficient depends only on `n` and `m`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 3.5, p.15.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. The index classes are the fibres of a surjective `cls : Fin n → ℤ_m²` (nonempty, disjoint, total
size `n`); the monomials of `H_m` are the assignment monomials `∏_{(i,j)} a_{ν_{ij},ν_{i+1,j},ν_{i,j+1}}`.
"Depends only on `n` and `m`" is the quantifier order: `κ` is chosen before the classes. -/
theorem theorem_3_5 (𝓡 : ResultantSystem) (m : ℕ) [NeZero m] (hm : 3 ≤ m) (n : ℕ) :
    ∃ κ : ℤ, κ ≠ 0 ∧ ∀ cls : Fin n → ZMod m × ZMod m, Function.Surjective cls →
      ∀ ν : (∀ p : ZMod m × ZMod m, {α // cls α = p}),
        (charCoeff 𝓡 n (m ^ 2)).coeff (assignMonomial cls ν) = κ := by sorry

end ResultantVNP
