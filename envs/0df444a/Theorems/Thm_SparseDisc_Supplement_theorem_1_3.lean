-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_1_3
-- name    : SparseDisc.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:08:04.87123+00:00
-- url     : https://prove2.me/theorems/a5d00c54-6ee1-44af-983d-049a4457a65d
-- title:
--   Theorem 1.3 — Berge-acyclic $t$-sparse families
-- statement:
--   Let $t\ge1$. If $F$ is a finite $t$-sparse family of $1$-Lipschitz set functions and its bundle hypergraph is Berge-acyclic, then
--   $$
--   \operatorname{disc}(F)\le K_t.
--   $$
--   This is tight in the supremum sense: for every $\varepsilon>0$ there is such a family with one bundle and discrepancy greater than $K_t-\varepsilon$.
--
--   The theorem identifies $K_t$ as the exact universal bound for acyclic sparsity patterns without asserting that the supremum is attained.
--
--   Differences from the source:
--   - encoding: finite families and item sets → functions and items indexed by finite Lean types, with discrepancy stated by the existence predicate `DiscLE`; reason: Lean convention, with the same finite families and colourings
--   - reading: a tight family with a single hyperedge for every $t\ge1$ → every item is relevant to all `Fin t` functions, giving one bundle; for $t=1$ it is private and for $t\ge2$ it is the single hyperedge; reason: the source defines hyperedges to have size at least two but states the tightness clause for all positive $t$
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 1.3, p.3

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_relevant
import Definitions.Def_SparseDisc_Supplement_IsTSparse
import Definitions.Def_SparseDisc_Supplement_BergeAcyclic
import Definitions.Def_SparseDisc_Supplement_K

namespace SparseDisc.Supplement

/-- **Theorem 1.3** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.3). A Berge-acyclic `t`-sparse family has
discrepancy at most `K t`, and the bound is sharp in the supremum sense: for every positive
`ε` there is a family with one bundle and discrepancy greater than `K t - ε`.

**Formalization Note** The functions and items are finite types. In the sharpness clause the
functions are `Fin t`, the items are `Fin m` with `m ≥ 1`, and every item is relevant to every
function, so there is exactly one bundle. This also covers `t = 1`, where that sole bundle is
private rather than a hyperedge. -/
theorem theorem_1_3 :
    (∀ (t : ℕ), 1 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ),
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → IsTSparse t f →
      BergeAcyclic (fun v => SparseDisc.relevant (f v)) → SparseDisc.DiscLE f (K t)) ∧
    (∀ (t : ℕ), 1 ≤ t → ∀ ε : ℝ, 0 < ε →
      ∃ (m : ℕ) (f : Fin t → Finset (Fin m) → ℝ), 1 ≤ m ∧
        (∀ v, SparseDisc.IsOneLipschitz (f v)) ∧ IsTSparse t f ∧
        (∀ j : Fin m, Finset.univ.filter
          (fun v => j ∈ SparseDisc.relevant (f v)) = Finset.univ) ∧
        BergeAcyclic (fun v => SparseDisc.relevant (f v)) ∧
        ¬ SparseDisc.DiscLE f (K t - ε)) := by sorry

end SparseDisc.Supplement
