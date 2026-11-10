-- Prove2me | Theorems.Thm_TwoConnSS_lemma_8_2
-- name    : TwoConnSS.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:57.090068+00:00
-- url     : https://prove2.me/theorems/cf982a79-10ea-4d89-b5ac-b79ffb3fc37b
-- title:
--   Lemma 8.2 — reduction of 2ECSS to $(\alpha,\eta)$-structured graphs
-- statement:
--   Let $6/5 \le \alpha \le 5/4$ and $0 < \eta \le 1/100$. Suppose a polynomial-time algorithm returns, on every $(\alpha,\eta)$-structured graph $G$, a 2ECSS $F$ of $G$ with
--   $$|F| \le \alpha \cdot \mathrm{opt}_E(G).$$
--   Then some polynomial-time algorithm returns, on every 2-edge-connected simple graph $G$, a 2ECSS $F$ with $|F| \le (\alpha + 4\eta)\,\mathrm{opt}_E(G)$.
--
--   This is the preprocessing reduction of Hommelsheim, Lindermayr and Liu [20, Lemma 3], which lets the paper's algorithms assume the structural exclusions of structured graphs.
--
--   Differences from the source:
--   - reading: (α, η)-structured graphs of [20, Definition 1] → `Structured α η`, the list of properties stated on p.32 with the preprocessing cut thresholds of p.32; reason: the paper records exactly these properties; [20]'s extra conditions, if any, only shrink [20]'s class, so the statement follows from [20, Lemma 3]
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4`, fixed before the instance, on the encodings `encIn`/`encOut` (n in unary, then the adjacency matrix; edge lists in binary); reason: Lean needs a machine model; the input length is at least n², so polynomial in the code length is polynomial in n
--   - encoding: opt_E(G), the minimum size of a 2ECSS → a comparison with every 2ECSS `F'` of `G`; reason: avoids the junk value of an infimum; same instances
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 8.2, p.32 (PDF p.33), citing [20, Lemma 3]

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_IsTwoECSS
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured

namespace TwoConnSS

/-- **Lemma 8.2 ([20, Lemma 3]): reduction to structured graphs.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 8.2, p.32: "For fixed
6/5 ≤ α ≤ 5/4 and 0 < η ≤ 1/100, a polynomial-time α-approximation for 2ECSS on (α, η)-structured
graphs yields a polynomial-time (α + 4η)-approximation for general 2ECSS."

Let `6/5 ≤ α ≤ 5/4` and `0 < η ≤ 1/100`. If some polynomial-time `alg` returns, on every instance
whose graph is `(α, η)`-structured, a 2ECSS with at most `α·|F'|` edges for every 2ECSS `F'`, then
some polynomial-time `alg'` returns, on every instance whose graph is 2EC, a 2ECSS with at most
`(α + 4η)·|F'|` edges for every 2ECSS `F'`.

**Formalization Note.** The result is cited from [20]. `Structured α η` is the list of p.32 (see its
docstring); [20, Definition 1] may add conditions, which only shrink [20]'s class and so make this
statement a consequence of [20, Lemma 3]. Machines as in Theorem 5.1. -/
theorem lemma_8_2 (α η : ℝ) (hα₁ : 6 / 5 ≤ α) (hα₂ : α ≤ 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    (∃ alg : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, Structured α η I.graph →
        IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
        ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
          ((toEdges I.n (alg I)).card : ℝ) ≤ α * (F'.card : ℝ)) →
    ∃ alg' : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg') ∧
      ∀ I : Inst, IsTwoEC I.graph →
        IsTwoECSS I.graph (toEdges I.n (alg' I)) ∧
        ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
          ((toEdges I.n (alg' I)).card : ℝ) ≤ (α + 4 * η) * (F'.card : ℝ) := by sorry

end TwoConnSS
