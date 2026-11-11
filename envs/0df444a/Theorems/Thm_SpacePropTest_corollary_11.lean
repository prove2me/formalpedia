-- Prove2me | Theorems.Thm_SpacePropTest_corollary_11
-- name    : SpacePropTest.corollary_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:04.147357+00:00
-- url     : https://prove2.me/theorems/0d14a1d9-b95f-42f0-8f03-55cbaa46be21
-- title:
--   Corollary 11, p.16 — if $A_f$ and $A_g$ are $1/(10M)$-indistinguishable for $f\in\mathcal P$ and $g$ $\varepsilon$-far, $A$ is not an $(\varepsilon,1/3)$-tester
-- statement:
--   Let $A$ be an $M$-state tester, $\mathcal P$ a property and $\varepsilon\in(0,1]$. Suppose there are functions $f,g$ with
--
--   1. $f\in\mathcal P$;
--   2. $g$ is $\varepsilon$-far from every function in $\mathcal P$;
--   3. $A_f$ and $A_g$ are $\frac1{10M}$-indistinguishable.
--
--   Then $A$ is not an $(\varepsilon,1/3)$-tester for $\mathcal P$.
--
--   Every lower bound of the paper ends by exhibiting such a pair.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Corollary 11, p.16 (PDF 18)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_Indist

set_option autoImplicit false

namespace SpacePropTest

/-- **Corollary 11** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.16 (PDF 18)).
Let `A` be an `M`-state tester and `P` a property. Suppose that there exist functions `f, g` such
that (1) `f ∈ P`; (2) `g` is `ε`-far from every function in `P`; and (3) `A_f` and `A_g` are
`1/(10M)`-indistinguishable. Then `A` is not an `(ε, 1/3)`-tester for `P`.

**Formalization Note.** `M = |σ|`; `ε ∈ (0, 1]`, the range of the `(ε, δ)`-tester definition
(p.16). -/
theorem corollary_11 {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ] (A : Tester n σ)
    (P : Set (BoolFn n)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (f g : BoolFn n) (hf : f ∈ P)
    (hg : IsFar P g ε) (hind : Indist (A.chain f) (A.chain g) (1 / (10 * Fintype.card σ))) :
    ¬ A.IsTester P ε (1 / 3) := by sorry

end SpacePropTest
