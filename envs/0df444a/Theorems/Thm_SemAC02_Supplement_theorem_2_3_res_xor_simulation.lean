-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_2_3_res_xor_simulation
-- name    : SemAC02.Supplement.theorem_2_3_res_xor_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:46:17.671229+00:00
-- url     : https://prove2.me/theorems/9cdefca1-b472-4048-bc21-0a4303224252
-- title:
--   Theorem 2.3 — semantic ΣΠΣ-PC simulates semantic Res(⊕)
-- statement:
--   Let $\varphi$ be a CNF formula on $n\ge1$ variables with polynomial encoding $F_\varphi=\{[\![C]\!]:C\in\varphi\}$ over $\mathbb F_2$. If $\varphi$ has an arity-2 semantic Res(⊕) refutation with $L$ lines, then $F_\varphi$ has an arity-2 semantic ΣΠΣ-PC refutation $\pi'$ such that
--
--   $$
--   S(\pi')\le L\qquad\text{and}\qquad \mathrm{size}(\pi')=O(nL),
--   $$
--
--   where $S(\pi')$ is the number of distinct non-zero product terms of $\pi'$ and $\mathrm{size}$ is the ΣΠΣ-size. The constant in $O(nL)$ is absolute.
--
--   The theorem transfers every lower bound on $S(\pi)$ for semantic ΣΠΣ-PC to semantic Res(⊕).
--
--   **Formalization Note** The ΣΠΣ-size is the number of distinct rooted subcircuits (`csize`).
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: size of a proof: distinct rooted subcircuits, sharing across lines → csize: distinct subterms of the lines; reason: a circuit term with equal subterms identified is the DAG with maximal sharing
--   - encoding: ΣΠΣ-size O(nL) → ∃ K : ℝ, chosen before n, φ and π, with csize π' ≤ K·n·L; reason: the O-constant is absolute
--   - encoding: Res(⊕) axiom line: a clause of φ with x_i as x_i = 1 and ¬x_i as x_i = 0 → IsSemResXorRef: a line that is a permutation of C.toList.map litLinEq for some C ∈ φ; lines are lists of (coefficient vector, right-hand side); reason: a linear clause is a disjunction, so the order of its equations is immaterial; same refutations
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 2.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_ResXor

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 2.3 (Simulation of Res(⊕))** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret,
*Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 2.3,
p.18): suppose that a CNF formula `φ` on `n ≥ 1` variables has a semantic Res(⊕) refutation with
`L` lines. Then `F_φ` has a semantic ΣΠΣ-PC refutation `π'` with `S(π') ≤ L`, where `S(π')` counts
its distinct non-zero product terms. Moreover, `π'` has ΣΠΣ-size `O(nL)`.

**Formalization Note** `O(nL)` is an absolute constant `K` chosen before `n`, `φ` and the
refutation. The ΣΠΣ-size is the `C`-size `csize` (distinct rooted subcircuits, p.15). Both
systems are arity-2 semantic systems over `𝔽₂`. -/
theorem theorem_2_3_res_xor_simulation :
    ∃ K : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (φ : LiftSAParity.CNF (Fin n))
      (π : List (LinClause (Fin n))), IsSemResXorRef φ π →
      ∃ π' : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        topS Set.univ π' ≤ π.length ∧
        (csize π' : ℝ) ≤ K * n * π.length := by sorry

end SemAC02.Supplement
