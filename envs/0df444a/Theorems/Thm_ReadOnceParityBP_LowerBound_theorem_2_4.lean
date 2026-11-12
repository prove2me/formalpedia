-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_theorem_2_4
-- name    : ReadOnceParityBP.LowerBound.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:45.419828+00:00
-- url     : https://prove2.me/theorems/51e9cadd-9d91-499f-a41e-77f1e10fbf8a
-- title:
--   Theorem 2.4 — syntactically multilinear circuit lower bound
-- statement:
--   Fix any field F, including characteristic two. There are c>0 and n₀≥2, uniform in the cycle length and circuit, such that for every even n≥n₀, every well-formed syntactically multilinear circuit Γ computing the polynomial f from Definition 2.3 over F has
--
--   $$|\Gamma|\ge\frac{c n^2}{(\log n)^2}.$$
--
--   Here f has n x-variables and n y-variables, and circuit size counts incoming wires. The constants may depend on F. This is the all-fields algebraic lower bound attributed in the submission to Raz–Shpilka–Yehudayoff and Alon–Kumar–Volk; it is a target to prove, not an assumption in the main theorem.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - encoding: size Ω(n²/log² n) → a positive real constant and a natural threshold at least two, quantified before n and the program, using the natural logarithm; reason: this is exactly the asymptotic statement; changing the logarithm base rescales the constant
--   - encoding: arithmetic DAG circuits with syntactic variable-disjoint products and edge size → topologically ordered gate lists, finite sum gates, binary products, and the total number of incoming wires; reason: topological numbering preserves sharing and syntactic supports; replacing larger products by binary trees preserves disjointness and changes wire size by at most a constant factor, absorbed in O and Ω
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 2.4 ([RSY08, AKV20]), p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_Circuit
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Theorem 2.4 ([RSY08, AKV20]) (p. 4): over any field `F`, every syntactically
multilinear circuit computing the polynomial `f` of Definition 2.3 has size
`Ω(n² / log² n)` (`n` even). -/
theorem theorem_2_4 (F : Type) [Field F] :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → Even n →
      ∀ Γ : Circuit (Fin n ⊕ Fin n) F, Γ.WellFormed → Γ.SyntacticallyMultilinear →
        Γ.Computes (rsyPoly F n) →
        c * (n : ℝ) ^ 2 / (Real.log n) ^ 2 ≤ (Γ.size : ℝ) := by sorry

end ReadOnceParityBP.LowerBound
