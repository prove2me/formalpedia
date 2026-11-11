-- Prove2me | Theorems.Thm_SpacePropTest_lemma_13
-- name    : SpacePropTest.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:10.587038+00:00
-- url     : https://prove2.me/theorems/7ea4bc5e-60a4-499e-80f0-76b3c0d96d04
-- title:
--   Lemma 13, p.17 — every $M$-state $(\varepsilon,\delta)$-tester has a $2M$-state $(\varepsilon,\delta)$-tester in normal form
-- statement:
--   Let $\varepsilon,\delta\in(0,1]$ and let $A$ be an $(\varepsilon,\delta)$-tester for a property $\mathcal P$ using $M$ states. Then there exists an $(\varepsilon,\delta)$-tester $A'$ for $\mathcal P$ in normal form (Definition 12) using exactly $2M$ states.
--
--   Normal form costs one bit of memory, so the lower bounds may assume it.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - reading: “using $2M$ states” → exactly $2M$ states; reason: the stronger of the two readings (exactly / at most)
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 13, p.17 (PDF 19); proof, p.55 (PDF 57)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 13** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity
of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.17 (PDF 19), proof p.55
(PDF 57)). Let `A` be an `(ε, δ)`-tester for a property `P` using `M` states. Then there exists an
`(ε, δ)`-tester `A'` in normal form using `2M` states.

**Formalization Note.** `M = |σ|`, and `A'` has exactly `2M` states; `ε, δ ∈ (0, 1]`, the range
of the `(ε, δ)`-tester definition (p.16). -/
theorem lemma_13 {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ] (A : Tester n σ)
    (P : Set (BoolFn n)) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : A.IsTester P ε δ) :
    ∃ (σ' : Type) (_ : Fintype σ') (_ : DecidableEq σ') (A' : Tester n σ'),
      Fintype.card σ' = 2 * Fintype.card σ ∧ A'.IsNormalForm ∧ A'.IsTester P ε δ := by sorry

end SpacePropTest
