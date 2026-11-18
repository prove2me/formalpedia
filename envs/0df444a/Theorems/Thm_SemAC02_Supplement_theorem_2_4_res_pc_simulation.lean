-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_2_4_res_pc_simulation
-- name    : SemAC02.Supplement.theorem_2_4_res_pc_simulation
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:47:03.319379+00:00
-- url     : https://prove2.me/theorems/a08d4d99-a9dd-48c3-975e-12243733ce13
-- title:
--   Theorem 2.4 — semantic ΣΠΣΠ-PC simulates semantic Res(PC) over any field
-- statement:
--   Let $\mathbb F$ be any field and $\phi$ a CNF formula with polynomial encoding $F_\phi$ over $\mathbb F$. If $\phi$ has an arity-2 semantic Res(PC) refutation $\pi$ in which every polynomial is written as a sum of monomials, then $F_\phi$ has an arity-2 semantic ΣΠΣΠ-PC refutation $\pi'$ with
--
--   1. total circuit size $O(\mathrm{size}(\pi))$, the constant absolute;
--   2. $S(\pi')\le L$ if $\pi$ has $L$ lines;
--   3. $\pi'$ a ΣΠΣΠ[$w$]-PC refutation whenever $\pi$ is a semantic Res(PC$_w$) refutation.
--
--   The simulation preserves the inference arity.
--
--   Lower bounds for semantic ΣΠΣΠ[w]-PC therefore apply to semantic Res(PC$_w$).
--
--   **Formalization Note** Total circuit size is `csize` (shared subcircuits) and $\mathrm{size}(\pi)$ is `resPCSize`. Both systems have arity 2, the arity the paper uses throughout.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - reading: total circuit size of π′ (the theorem does not say whether subcircuits shared across lines are counted once) → csize: distinct subterms across all lines (the C-size of p.15, sharing across lines); reason: the proof reuses shared polynomial subcircuits across the derivation (p.19); the per-line sum |π|₄ of (32) can exceed size(π) by a factor L when one polynomial occurs in many lines, so only the sharing reading makes the statement true
--   - reading: size(π) counts distinct rooted subcircuits across the derivation → resPCSize counts distinct lines, polynomials, monomials and variables; reason: each line is the gate joining its polynomials; the proof adds O(1) gates per distinct line, so the lines are counted
--   - reading: axiom lines are the clauses of ϕ → literal x_i written as 1 − x_i = 0, ¬x_i as x_i = 0 (litPolyF), in any order; reason: the paper's truth-value polynomials (p.14); the translated axiom is then ⟦C⟧
--   - reading: Res(PC_w): every polynomial has degree at most w → totalDegree of each displayed polynomial ≤ w; reason: the degree of the polynomial as written; this is what gives bottom fan-in ≤ w
--   - encoding: the simulation preserves the inference arity → π and π' are both arity-2 semantic refutations; reason: the paper uses arity 2 throughout (p.16)
--   - encoding: total circuit size O(size(π)) → ∃ K : ℝ chosen before the field, csize π' ≤ K·resPCSize π; reason: the O-constant is absolute
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 2.4, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_ResPC

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 2.4 (Simulation of Res(PC))** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret,
*Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 2.4,
p.19): let `F` be any field and `ϕ` a CNF formula. Suppose that `ϕ` has a semantic Res(PC)
refutation `π`, every polynomial represented explicitly as a sum of monomials. Then the polynomial
encoding `F_ϕ` has a semantic ΣΠΣΠ-PC refutation `π'` of total circuit size `O(size(π))`. The
simulation preserves the inference arity. If `π` has `L` lines, then `S(π') ≤ L`. If `π` is a
semantic Res(PC_w) refutation, then `π'` is a semantic ΣΠΣΠ[w]-PC refutation.

**Formalization Note** `O(size(π))` is an absolute constant `K` chosen before the field. The total
circuit size of `π'` is its `C`-size `csize` (sharing across lines) and `size(π)` is `resPCSize`.
Both systems are arity-2 semantic systems (the paper uses arity 2 throughout, p.16), which is the
preserved arity. Res(PC_w): every polynomial of `π` has degree at most `w`. -/
theorem theorem_2_4_res_pc_simulation :
    ∃ K : ℝ, ∀ (F : Type) [Field F] (n : ℕ) (φ : LiftSAParity.CNF (Fin n))
      (π : List (List (MvPolynomial (Fin n) F))), IsSemResPCRef φ π →
      ∃ π' : List (ACirc F (Fin n)),
        IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        (csize π' : ℝ) ≤ K * resPCSize π ∧
        topS Set.univ π' ≤ π.length ∧
        ∀ w : ℕ, (∀ D ∈ π, ∀ f ∈ D, f.totalDegree ≤ w) → ∀ c ∈ π', IsSPSP (w : ℕ∞) c := by sorry

end SemAC02.Supplement
