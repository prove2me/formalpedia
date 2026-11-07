-- Prove2me | Theorems.Thm_ReadTwiceCount_lemma_2_1
-- name    : ReadTwiceCount.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:36.169099+00:00
-- url     : https://prove2.me/theorems/83f9dcfc-c848-47be-8016-0937e2b0c1ae
-- title:
--   Lemma 2.1 — unit propagation decides satisfiability of read-twice formulas in polynomial time
-- statement:
--   **Lemma 2.1.** Unit propagation decides satisfiability of a read-twice CNF formula in polynomial time. Precisely:
--
--   1. **Correctness.** Let $F$ be a read-twice normalized formula, and let $G$ be obtained from $F$ by a sequence of unit-propagation steps after which propagation has terminated (an empty clause appeared, or no unit clause is left). Then
--   $$Z(F)>0\iff G\text{ has no empty clause}.$$
--   2. **Polynomial time.** There are a Turing machine $T$ and a constant $c$ such that, on the encoding of every read-twice formula $F$, $T$ outputs the bit $[Z(F)>0]$ within $c\,(N+1)^c$ steps, where $N$ is the encoding length.
--
--   This is the exact feasibility test the algorithm uses for its zero tests: whether a state is satisfiable and whether a queried marginal is zero.
--
--   Differences from the source:
--   - reading: "Unit propagation decides satisfiability of a read-twice CNF formula in polynomial time" → (1) on read-twice normalized $F$, every terminated propagation $G$ has no empty clause iff $Z(F)>0$; (2) one `TM2` machine and one constant $c$ decide $Z(F)>0$ for every read-twice $F$ within $c(N+1)^c$ steps; reason: the lemma asserts both that the propagation test is correct (normalization is the algorithm's first step, §2, p.2) and that it runs in polynomial time; the paper fixes no machine, and a `TM2` simulates a bit-operation algorithm with polynomial overhead
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 2.1, p.2

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ReadTwiceCount_encodeFormula
import Definitions.Def_ReadTwiceCount_UPStep

namespace ReadTwiceCount

/-- **Lemma 2.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Lemma 2.1, p.2): "Unit propagation decides
satisfiability of a read-twice CNF formula in polynomial time."

Two parts:
1. *Correctness of unit propagation.* If `F` is read-twice and normalized and `G` is obtained from `F` by any
   sequence of unit-propagation steps that has terminated (an empty clause appeared, or no unit clause
   is left), then `F` is satisfiable iff `G` has no empty clause.
2. *Polynomial time.* One Turing machine `T` and one constant `c` decide satisfiability of every
   read-twice formula within `c·(N + 1)^c` steps.

**Formalization Note** Part 1 is for normalized formulas: the algorithm normalizes first (§2, p.2),
which preserves the count. Part 2 takes every read-twice formula as input. The machine is Mathlib's
`TM2` with Boolean alphabets; its output is the single bit `decide (0 < Z F)`. -/
theorem lemma_2_1 :
    (∀ {M : ℕ} (F G : Formula M), ReadTwice F → Normalized F →
        Relation.ReflTransGen UPStep F G → UPTerminal G → (0 < Z F ↔ [] ∉ G.clauses)) ∧
    ∃ (T : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (M : ℕ) (F : Formula M), ReadTwice F →
      HMBinPacking.OutputsWithin T (encodeFormula F) [decide (0 < Z F)] (c * (N F + 1) ^ c) := by sorry

end ReadTwiceCount
