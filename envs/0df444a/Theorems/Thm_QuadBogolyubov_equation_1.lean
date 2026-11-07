-- Prove2me | Theorems.Thm_QuadBogolyubov_equation_1
-- name    : QuadBogolyubov.equation_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:01:21.699948+00:00
-- url     : https://prove2.me/theorems/389c2c05-9f09-4ddd-a70b-4d394f1a7521
-- title:
--   Eq. (1) — quadratic polynomials vanish on Gowers $U^3$ cubes
-- statement:
--   For every quadratic polynomial $q:\mathbb F_2^n\to\mathbb F_2$ and all $x,h_1,h_2,h_3\in\mathbb F_2^n$,
--   $$q(x)=\sum_{\omega\in\{0,1\}^3\setminus\{0\}}q(x+\omega_1h_1+\omega_2h_2+\omega_3h_3).$$
--   This is the vanishing of third discrete derivatives, and it is what produces the seven-point identity of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the universal quantifiers over x, h₁, h₂, h₃ are implicit in the display → explicit, with h : Fin 3 → 𝔽₂ⁿ and ω : Fin 3 → ZMod 2; reason: Lean convention; the proof on p.15 applies it at arbitrary points
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: quadratic polynomial q : F₂ⁿ → F₂ → `IsQuadraticPoly q`: evaluation of an `MvPolynomial` of total degree ≤ 2, constant and linear terms included; reason: the literal meaning of "polynomial of degree at most two"
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §2.2.1, p.6, eq. (1)

import Mathlib
import Definitions.Def_QuadBogolyubov_IsQuadraticPoly

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Eq. (1): quadratic polynomials vanish on Gowers `U³` cubes.** For every quadratic polynomial
`q : 𝔽₂ⁿ → 𝔽₂` and all `x, h₁, h₂, h₃ ∈ 𝔽₂ⁿ`,
`q(x) = ∑_{ω ∈ {0,1}³ \ {0}} q(x + ω₁h₁ + ω₂h₂ + ω₃h₃)`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §2.2.1, p.6, eq. (1): "Observe that every quadratic polynomial q : F₂ⁿ → F2 vanishes when
summed over the Gowers U3 cube; that is, (1) q(x) = Σ_{ω∈{0,1}³\{0}} q(x + ω1h1 + ω2h2 + ω3h3)."

**Formalization Note.** `ω ∈ {0,1}³` is `Fin 3 → ZMod 2` and `(h₁, h₂, h₃)` is
`h : Fin 3 → 𝔽₂ⁿ`; the sum is in `𝔽₂ = ZMod 2`. -/
theorem equation_1 {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) (hq : IsQuadraticPoly q)
    (x : Fin n → ZMod 2) (h : Fin 3 → (Fin n → ZMod 2)) :
    q x = ∑ ω ∈ Finset.univ.filter (fun ω : Fin 3 → ZMod 2 => ω ≠ 0),
      q (x + ∑ i, ω i • h i) := by sorry

end QuadBogolyubov
