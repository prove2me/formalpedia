-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_las_vegas_decoder
-- name    : QuantumGroupCodes836.Addressability.las_vegas_decoder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:50.2981+00:00
-- url     : https://prove2.me/theorems/8c043441-678d-4192-801b-8a87ac5e385f
-- title:
--   Theorem 4.7 — Las Vegas decoder and exact integer radius
-- statement:
--   Fix a prime power $q>4$. There is a positive constant $C_q$, uniform over all source function fields and codes. Under every hypothesis of Theorem 4.1, choose the actual rate-preserving AG lift over the quadratic constant field, of length $\widetilde n$ and genus $\widetilde g$. A uniform operational decoder exists with
--
--   $$R=|G|\left\lfloor\frac{n-\deg D+g-1}{2}\right\rfloor-\widetilde g,\qquad\mathbb E[T]\le C_q\widetilde n^2(\log\widetilde n)^4.$$
--
--   Correctness is required for every natural error weight at most the integer $R$, even when that condition is empty for a small code. The floor precedes multiplication by $|G|$ and the subtraction is not truncated. The same constant bounds reusable auxiliary storage. No unknown error is supplied to the program.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - reading: Las Vegas decoding with polylogarithmic time → almost-sure termination, correctness of every terminating run and expected charged cost with log exponent four; reason: footnotes 3 and 7 fix the exponent; a finite-field RAM consumes independent uniform symbols and counts every operation and output read
--   - encoding: a classical received-word decoder → a uniform program receiving only syndrome and immutable code data; reason: a precomputed linear right inverse reconstructs a received-word representative in quadratic field work; reusable auxiliary storage is bounded and per-call reads and computation are charged
--   - generalization: the constants in the proof of Theorem 4.1 → alpha_q=log(sqrt(q)-1)/(q+1+2sqrt(q)), beta_q=log((q+1)/(sqrt(q)-1)); reason: p.18 supplies these explicit positive witnesses for the existential constants of Theorem 4.1; the Lean bounds imply the source existential ones
--   - encoding: an integer m and a differential η with the stated simple poles → 0 < m and η ≠ 0 (inside AGAssumptions); reason: Definition 2.7 defines the m-multiplication property, which the theorem asserts, only for m ≥ 1; the zero differential has no divisor or poles
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 4.7, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem las_vegas_decoder (q : ℕ) (hq : 4 < q)
    (hPrimePower : ∃ p s : ℕ, p.Prime ∧ 0 < s ∧ q = p ^ s) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ (k : Type) [Field k] [Fintype k], Fintype.card k = q →
      ∀ (l : Type) [Field l] [Fintype l] [Algebra k l], Fintype.card l = q ^ 2 →
      ∃ program : DecoderProgram l, ∀ (F : FunctionFieldData k) (P : EvaluationData F) (D : Divisors F)
      (m : ℕ) (η : KaehlerDifferential k F.carrier),
      1 < genus F → 2 * genus F < Nat.card {R : Places F // R.deg = 1} →
      2 * genus F < P.n → effective D → AGAssumptions P D m η →
      (∀ R : Places F, R.deg = 1 → R.ordDifferential η = -1) →
      ∃ L : LiftData F, LiftCodeProperties P D m L ∧
        (Real.log (Real.sqrt q - 1) / (q + 1 + 2 * Real.sqrt q)) * P.n ≤ Real.log (Nat.card L.group) ∧
        Real.log (Nat.card L.group) ≤ Real.log ((q + 1) / (Real.sqrt q - 1)) * P.n ∧
        ∃ alphabetEquiv : l ≃ₐ[k] L.constants,
        ∃ auxiliary : List l,
          let cost := Cq * (L.evaluation.n : ℝ)^2 * (Real.log L.evaluation.n)^4
          auxiliary.length ≤ cost ∧
          Decodes (ClassicalCSS (agCode L.evaluation (conorm L.extension D))) .X (mapDecoderProgram alphabetEquiv.toEquiv program) (auxiliary.map alphabetEquiv)
            ((Nat.card L.group : ℤ) * (((P.n : ℤ) - AlgebraicCurve.Divisor.degree D + genus F - 1) / 2) -
              genus L.upstairs) cost := by sorry

end QuantumGroupCodes836.Addressability
