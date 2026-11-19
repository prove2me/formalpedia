-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_7_14_complete_unary_php
-- name    : SemAC02.Supplement.theorem_7_14_complete_unary_php
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:55:28.565705+00:00
-- url     : https://prove2.me/theorems/c87a83e9-7869-4b94-a04a-b38ecf74ec64
-- title:
--   Theorem 7.14 — PHP^{2n}_n needs semantic ΣΠΣΠ-PC size exp(γ(ln n)²/ln ln n)
-- statement:
--   For every fixed $0<\gamma<1/2$ and all sufficiently large $n$, every arity-2 semantic ΣΠΣΠ-PC refutation of the unary pigeonhole principle $\mathrm{PHP}^{2n}_n$ over $\mathbb F_2$ has total circuit size at least
--
--   $$
--   \exp\Bigl(\gamma\,\frac{(\ln n)^2}{\ln\ln n}\Bigr).
--   $$
--
--   The bottom fan-in is unrestricted; the bound is obtained by sparsifying to the expander instances of Theorem 7.5.
--
--   **Formalization Note** Total circuit size is `csize`, the number of distinct rooted subcircuits of the proof.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - generalization: total circuit size → csize (shared subcircuits); reason: csize ≤ |π|₄, so the bound for csize implies the bound for |π|₄; Lemma 7.13's count of bottom gates is a count of distinct gates
--   - encoding: all sufficiently large n → ∃ n₀ depending on γ, ∀ n ≥ n₀; reason: threshold as explicit quantifier
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 7.14, p.59 (PDF p.61)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_fphpG
import Definitions.Def_SemAC02_Supplement_phpG

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 7.14 (Complete unary PHP)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Theorem 7.14,
p.59): for every fixed `0 < γ < 1/2` and all sufficiently large `n`, every semantic ΣΠΣΠ-PC
refutation of `PHP^{2n}_n` has total circuit size at least `exp(γ (ln n)² / ln ln n)`.

**Formalization Note** `PHP^{2n}_n = PHP(K_{2n,n})` over `𝔽₂` (§7.2, p.52), with unrestricted bottom
fan-in. Total circuit size is the `C`-size `csize` (distinct rooted subcircuits), which is at most
`|π|₄`, so this is the stronger form. `n₀` depends on `γ`. -/
theorem theorem_7_14_complete_unary_php (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ π : List (ACirc (ZMod 2) (Edge (completeBip (2 * n) n))),
        IsSemPCRef (IsSPSP ⊤) Set.univ (polyAx (phpG (completeBip (2 * n) n))) π →
        Real.exp (γ * Real.log n ^ 2 / Real.log (Real.log n)) ≤ csize π := by sorry

end SemAC02.Supplement
