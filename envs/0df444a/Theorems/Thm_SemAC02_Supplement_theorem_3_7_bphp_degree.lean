-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_3_7_bphp_degree
-- name    : SemAC02.Supplement.theorem_3_7_bphp_degree
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:48:21.454106+00:00
-- url     : https://prove2.me/theorems/b1978e57-8eec-451a-95de-1a9fb6c3f5a5
-- title:
--   Theorem 3.7 — semantic PC refutations of BPHP^m_n need degree n/6
-- statement:
--   For all sufficiently large $n=2^\ell$ and every $m>n$, every arity-2 semantic polynomial calculus refutation of $\mathrm{BPHP}^m_n$ over $\mathbb F_2$ has a line of degree at least
--
--   $$
--   \frac n6,
--   $$
--
--   the degree of a line being the degree of its multilinear representative.
--
--   This degree lower bound is the base case of the restriction argument for Theorem 3.2.
--
--   **Formalization Note** Semantic PC has arbitrary polynomials as lines; they are represented by arbitrary algebraic circuits, whose values are exactly the elements of $B_n(\mathbb F_2)$.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: lines are polynomials in B_n(F2) → lines are arbitrary ACirc circuits (class fun _ => True), degree fnDeg of the value; reason: every element of B_n is computed by a circuit; the refutation notion depends only on values
--   - encoding: for all sufficiently large n = 2^ℓ → ∃ ℓ₀, ∀ ℓ ≥ ℓ₀; reason: threshold as explicit quantifier
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 3.7, p.22 (PDF p.24); restated in Appendix A, p.70 (PDF p.72)

import Mathlib
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_bphp

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 3.7** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong
Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 3.7, p.22; restated and proved
in Appendix A, p.70): for all sufficiently large `n = 2^ℓ` and any `m > n`, any semantic polynomial
calculus refutation of `BPHP^m_n` over `𝔽₂` requires degree `n/6`.

**Formalization Note** Semantic polynomial calculus (p.16) has arbitrary polynomials as lines:
here lines are arbitrary algebraic circuits (class `fun _ => True`), whose values are exactly the
elements of `B_n(𝔽₂)`; the degree of a line is the degree of its multilinear representative
(`fnDeg`), and "requires degree `n/6`" means that some line has degree at least `n/6`. The
threshold `ℓ₀` is chosen before `ℓ` and `m`. -/
theorem theorem_3_7_bphp_degree :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π →
        ∃ c ∈ π, ((2 : ℝ) ^ ℓ) / 6 ≤ (fnDeg (cval c) : ℝ) := by sorry

end SemAC02.Supplement
