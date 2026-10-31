-- Prove2me | Theorems.Thm_ResistantSets_theorem_1_8
-- name    : ResistantSets.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:28.808985+00:00
-- url     : https://prove2.me/theorems/76ef24dd-ee6f-4a11-9b5b-2141ce8230d8
-- title:
--   Theorem 1.8 — resistance is excluding fragile and $\{\mathbf 0^k,\mathbf 1^k-e_1\}$ restrictions, or fragile minors
-- statement:
--   Let $n\ge1$ and $S\subseteq\{0,1\}^n$. The following statements are equivalent:
--
--   1. $S$ is resistant;
--   2. $S$ has no fragile restriction, and for no $k\ge4$ does $S$ have a $\{\mathbf 0^k,\mathbf 1^k-e_1\}$ restriction;
--   3. $S$ has no fragile minor.
--
--   Here $\{\mathbf 0^k,\mathbf 1^k-e_1\}\subseteq\{0,1\}^k$ is the two-point set consisting of the all-zeros vector and the vector whose coordinates are all $1$ except the first. Restrictions and minors are taken up to isomorphism.
--
--   This is the excluded-restriction and excluded-minor characterization of resistant sets; the propagation lemmas of §4 are derived from it.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: (i), (ii), (iii) are equivalent → (i ↔ ii) ∧ (i ↔ iii); reason: the same three-way equivalence
--   - encoding: S has no fragile minor → no minor S ι a J with ι : Fin 3 ↪ Fin n is fragile; reason: fragile sets are 3-dimensional and closed under isomorphism; ι may relabel
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Theorem 1.8, pp.4–5 (PDF pp.5–6)

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_minor
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_IsFragile

namespace ResistantSets

/-- **Theorem 1.8** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), pp.4–5): "Take an integer n ≥ 1 and a set S ⊆ {0,1}ⁿ. Then the
following statements are equivalent: (i) S is resistant, (ii) S has no fragile restriction and no
{0ᵏ, 1ᵏ − e₁}, k ≥ 4 isomorphic restriction, (iii) S has no fragile minor."

Stated as (i) ↔ (ii) and (i) ↔ (iii). `{0ᵏ, 1ᵏ − e₁} ⊆ {0,1}ᵏ` is the two-point set
`{fun _ => false, fun i => decide (i.val ≠ 0)}` (the second point has every coordinate `1`
except the first).

**Formalization Note** "Restriction" and "minor" are isomorphic ones (footnote 3, p.5). A fragile
restriction is `HasRestriction S F` for a fragile `F ⊆ {0,1}³`; since fragility is closed under
isomorphism, a fragile minor is a minor `minor S ι a J ⊆ {0,1}³` (whose `ι` may relabel) that
is fragile. -/
theorem theorem_1_8 {n : ℕ} (hn : 1 ≤ n) (S : Finset (Fin n → Bool)) :
    (IsResistant S ↔
      ((¬ ∃ F : Finset (Fin 3 → Bool), IsFragile F ∧ HasRestriction S F) ∧
        ∀ k : ℕ, 4 ≤ k →
          ¬ HasRestriction S
              ({fun _ => false, fun i => decide (i.val ≠ 0)} : Finset (Fin k → Bool)))) ∧
    (IsResistant S ↔
      ¬ ∃ (ι : Fin 3 ↪ Fin n) (a : Fin n → Bool) (J : Finset (Fin n)),
          IsFragile (minor S ι a J)) := by sorry

end ResistantSets
