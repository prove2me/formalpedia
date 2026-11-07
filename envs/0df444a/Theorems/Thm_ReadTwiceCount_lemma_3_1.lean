-- Prove2me | Theorems.Thm_ReadTwiceCount_lemma_3_1
-- name    : ReadTwiceCount.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:06.599118+00:00
-- url     : https://prove2.me/theorems/c19b74e6-1a41-4157-b858-a96631de15ea
-- title:
--   Lemma 3.1 — $1\le y(H,h)\le s+1$ and $p(H,h)\ge 1/(s+2)$
-- statement:
--   **Lemma 3.1.** Every positive dangling query $h$ in a read-twice normalized state $H$ with $s$ clauses satisfies
--   $$1\le y(H,h)\le s+1,\qquad p(H,h)\ge\frac{1}{s+2}.$$
--
--   The bound is exact: the $s$ clauses $(h\vee x_1),(\neg x_1\vee x_2),\dots,(\neg x_{s-1}\vee x_s)$ have coordinate $s+1$. This polynomial range of the coordinate is what the block construction and the cut values $s_u+1$ rest on.
--
--   Differences from the source: none.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 3.1, display (7), p.4

import Mathlib
import Definitions.Def_ReadTwiceCount_pFalse

namespace ReadTwiceCount

/-- **Lemma 3.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Lemma 3.1, p.4): "Every positive dangling
query in a state with s clauses satisfies 1 ≤ y(H, h) ≤ s + 1, p(H, h) ≥ 1/(s + 2)." (7)

**Formalization Note** States are read-twice and normalized, the paper's standing assumptions (§2,
p.2). -/
theorem lemma_3_1 {M : ℕ} (H : Formula M) (h : Lit M) (hRT : ReadTwice H) (hN : Normalized H)
    (hD : IsDangling H h) (hP : IsPositive H h) :
    1 ≤ yCoord H h ∧ yCoord H h ≤ (H.clauses.length : ℚ) + 1 ∧
      1 / ((H.clauses.length : ℚ) + 2) ≤ pFalse H h := by sorry

end ReadTwiceCount
