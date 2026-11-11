-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_C_2
-- name    : SeedRecyclingDL.Codes.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:31.997081+00:00
-- url     : https://prove2.me/theorems/9ea7cf11-7a25-403e-b979-827d49abb31c
-- title:
--   Lemma C.2 — Deterministic root finding
-- statement:
--   Let $b\ge1$ and let $R\ne0$ be a degree-$d$ polynomial over the binary polynomial-basis field $\mathbb F_{2^b}$. Procedure C.1 returns every root of $R$ in that field, with no repetitions. Finite uniform programs realize its output with
--   $$O(1+b^2d^2)\ \text{field operations},\qquad O(b^2+b^4d^2)\ \text{bit operations}.$$
--   Constants and both programs precede the field, representation, and polynomial. Degree zero returns the empty list. Modular squaring, gcds, and trace splitting define the procedure; an all-field root scan is not a primitive. This is the first-stage bad-seed computation.
--
--   Differences from the source:
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma C.2, printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_FieldExecution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_C_2 :
    ∃ (fieldProgram : List FieldInstruction) (bitProgram : Program) (C : ℝ), 0 < C ∧
      ∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F), P.p = 2 →
        ∀ R : Polynomial F, R ≠ 0 →
          (∀ a : F, a ∈ procedureC1 P R ↔ R.eval a = 0) ∧
          (procedureC1 P R).Nodup ∧
          FieldExecutes P fieldProgram P.k [R.natDegree]
            (P.generator :: coefficientList R) (procedureC1 P R)
            (C * (1 + (P.k : ℝ) ^ 2 * (R.natDegree : ℝ) ^ 2)) ∧
          Executes bitProgram P.k (rootInput P R)
            (some ((procedureC1 P R).map (fieldIndex P)))
            (C * ((P.k : ℝ) ^ 2 + (P.k : ℝ) ^ 4 * (R.natDegree : ℝ) ^ 2))
          := by sorry

end SeedRecyclingDL.Codes
