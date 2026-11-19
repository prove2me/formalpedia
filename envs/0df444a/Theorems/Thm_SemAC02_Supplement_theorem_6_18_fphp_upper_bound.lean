-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_6_18_fphp_upper_bound
-- name    : SemAC02.Supplement.theorem_6_18_fphp_upper_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:52:12.840409+00:00
-- url     : https://prove2.me/theorems/222e262d-7604-4447-bced-b7fc563c8032
-- title:
--   Theorem 6.18 — FPHP^{n+1}_n has semantic ΣΠΣΠ[2]-PC refutations of size O(n³ log(n+1))
-- statement:
--   The functional pigeonhole principle $\mathrm{FPHP}^{n+1}_n$ has an arity-2 semantic ΣΠΣΠ[2]-PC refutation over $\mathbb F_2$ of size
--
--   $$
--   O\bigl(n^3\log(n+1)\bigr),
--   $$
--
--   with an absolute constant. Consequently, the same upper bound holds in semantic ΣΠΣΠ[$w$]-PC for every $w\ge2$.
--
--   Together with Corollary 6.13 this separates semantic ΣΠΣΠ[2]-PC from semantic ΣΠΣ-PC.
--
--   **Formalization Note** The size is `csize`, for every $n\ge1$; the second sentence says that the same refutation consists of ΣΠΣΠ[$w$] lines.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: size of a proof: distinct rooted subcircuits, sharing across lines → csize: distinct subterms of the lines; reason: a circuit term with equal subterms identified is the DAG with maximal sharing
--   - encoding: size O(n³ log(n+1)) → ∃ K : ℝ, ∀ n ≥ 1, csize π ≤ K·n³·log(n+1); reason: the O-constant is absolute; n ≥ 1 because log 1 = 0
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 6.18, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_fphpG

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 6.18 (Functional pigeonhole principle)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 6.18, p.49): the principle `FPHP^{n+1}_n` has a semantic ΣΠΣΠ[2]-PC refutation over `𝔽₂`
of size `O(n³ log(n + 1))`. Consequently, the same upper bound holds in semantic ΣΠΣΠ[w]-PC for
every `w ≥ 2`.

**Formalization Note** `FPHP^{n+1}_n = FPHP(K_{n+1,n})` (Definition 6.6); `O(·)` is an absolute
constant `K`, the bound holding for every `n ≥ 1`. The size is the `C`-size `csize`. The second
sentence: the same refutation is a ΣΠΣΠ[w]-PC refutation for every `w ≥ 2`. -/
theorem theorem_6_18_fphp_upper_bound :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ π : List (ACirc (ZMod 2) (Edge (completeBip (n + 1) n))),
        IsSemPCRef (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n + 1) n))) π ∧
        (csize π : ℝ) ≤ K * (n : ℝ) ^ 3 * Real.log ((n : ℝ) + 1) ∧
        ∀ w : ℕ, 2 ≤ w → ∀ c ∈ π, IsSPSP (w : ℕ∞) c := by sorry

end SemAC02.Supplement
