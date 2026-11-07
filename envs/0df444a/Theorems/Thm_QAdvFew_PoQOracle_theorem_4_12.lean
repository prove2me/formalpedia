-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_4_12
-- name    : QAdvFew.PoQOracle.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:51.583523+00:00
-- url     : https://prove2.me/theorems/0029e7c2-73e5-4f09-b9ea-549ed949327a
-- title:
--   Theorem 4.12 — weak hardness of salted majority
-- statement:
--   There is a universal constant $\delta$ such that with probability $1$ over $O\leftarrow\mathcal D$: for every polynomial $p$ and every family $\{C^O_n\}$ of circuits of size $p(n)$, for all sufficiently large $n$,
--   $$\Pr_{x\leftarrow\{0,1\}^n}[C^O_n(x)=h^O(x)]\le1-\delta.$$
--
--   This is the paper's main hardness result, and the oracle-relative hardness behind all of its proofs of quantumness.
--
--   Differences from the source:
--   - generalization: the oracle distribution D built from the Forrelation distribution of [RT19] → D built from any family F with the properties of Lemma 3.10 used; reason: the construction of [RT19] is one such family by Lemma 3.10, and the paper's proof uses only these properties
--   - reading: a universal constant δ → δ ∈ (0, 1), chosen before the family F; reason: the proof obtains δ from the constant β of Lemma 4.11, which does not depend on F
--   - encoding: circuits of size p(n) → oracle circuits of size at most p(n), quantified after the seed; reason: the paper pads to size exactly p(n), and circuits may depend on O
--   - reading: machines of S_t syntactically restricted to query levels up to ⌊√t⌋ and to the time and space bounds → every pair of code length below t, run with the truncated oracle and clocks; reason: makes the recursion well-founded; same value on machines obeying the restrictions
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 4.12, p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_saltedMaj
import Definitions.Def_QAdvFew_PoQOracle_ForrAC0

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Theorem 4.12 (Weak hardness of salted majority)** (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 4.12, p. 27 (PDF p. 29)).
There is a universal constant `δ` such that with probability 1 over `O ← D`: for every polynomial `p`
and every family `{C^O_n}` of circuits of size `p(n)`, for all sufficiently large `n`,
`Pr_{x←{0,1}^n}[C^O_n(x) = h^O(x)] ≤ 1 − δ`.

**Formalization Note** `δ ∈ (0, 1)` is chosen before the family `F` (property (2) of Lemma 3.10)
from which `D` is built. The circuits are oracle circuits with the joined oracle `O`, size at most
`p(n)`, quantified after the seed so they may depend on `O`; `h^O` is salted majority of the seed's
random oracle. -/
theorem theorem_4_12 : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ (F : (N : ℕ) → PMF (Fin N → Bool)), ForrAC0 F →
    ∀ᵐ ω ∂(seedMeasure F), ∀ (p : Polynomial ℕ) (C : (n : ℕ) → Circuit (Fin n)),
      (∀ n, (C n).size ≤ p.eval n) →
      ∀ᶠ n in Filter.atTop,
        ((Finset.univ.filter (fun x : Fin n → Bool =>
            (C n).eval1 (sampleO ⊤ ω) x = saltedMaj (roOf ω) (List.ofFn x))).card : ℝ) / 2 ^ n ≤
          1 - δ := by sorry

end QAdvFew.PoQOracle
