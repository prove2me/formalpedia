-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_4_1
-- name    : QAdvFew.PoQOracle.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:20.003179+00:00
-- url     : https://prove2.me/theorems/2a846899-37d9-4dee-b800-464722e6b360
-- title:
--   Theorem 4.1 — the oracle distribution
-- statement:
--   There is a distribution over triples of classical oracles $O=(A,B,C)\leftarrow\mathcal D$ such that with probability $1$:
--
--   1. $\mathsf P^O=\mathsf{NP}^O$;
--   2. $\mathsf{BQP}^O=\mathsf{PSPACE}^O$;
--   3. $\mathsf{IP}^A=\mathsf{PSPACE}^A$;
--   4. there are a constant $\delta\in(0,1)$ and a Boolean function $f:\{0,1\}^*\to\{0,1\}$ such that
--      (a) for all nonuniform PPT algorithms $\mathcal A$, for all sufficiently large $n$, $\Pr_{x\leftarrow\{0,1\}^n}[\mathcal A^O(x)=f(x)]\le1-\delta$, and
--      (b) the language $L^f=\{x:f(x)=1\}$ is in $\mathsf{PSPACE}^A\subseteq\mathsf{IP}^O$.
--
--   This is the complexity-theoretic half of the paper's main theorem, in distributional form.
--
--   **Formalization Note** $O$ is the join of $(A,B,C)$. The distribution is existential, as in the paper; its construction appears in the other milestones.
--
--   Differences from the source:
--   - reading: the language is in PSPACE^A ⊆ IP^O → L^f ∈ PSPACE^A, L^f ∈ IP^O, and the inclusion PSPACE^A ⊆ IP^O; reason: all three things the display asserts
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 4.1, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_join3
import Definitions.Def_QAdvFew_PoQOracle_P
import Definitions.Def_QAdvFew_PoQOracle_NP
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_BQP
import Definitions.Def_QAdvFew_PoQOracle_IP
import Definitions.Def_QAdvFew_PoQOracle_NUAlg

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Theorem 4.1** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Theorem 4.1, p. 21 (PDF p. 23)). There is a distribution over
triples of classical oracles `O = (A, B, C) ← D` such that with probability 1,
1. `P^O = NP^O`;
2. `BQP^O = PSPACE^O`;
3. `IP^A = PSPACE^A`;
4. there are a constant `δ ∈ (0, 1)` and a boolean function `f : {0,1}* → {0,1}` such that
   (a) for all nonuniform PPT algorithms `A`, for all sufficiently large `n`,
   `Pr_{x←{0,1}^n}[A^O(x) = f(x)] ≤ 1 − δ`, and
   (b) the language `L^f = {x : f(x) = 1}` is in `PSPACE^A ⊆ IP^O`.

**Formalization Note** The distribution is any probability measure on triples of oracles, the
statement existential like the paper's; `O` is the joined oracle `join3 A B C`. Clause 4(b) is
`L^f ∈ PSPACE^A`, `L^f ∈ IP^O`, and the inclusion `PSPACE^A ⊆ IP^O` that its display asserts. -/
theorem theorem_4_1 : ∃ μ : Measure (Oracle × Oracle × Oracle), IsProbabilityMeasure μ ∧
    ∀ᵐ ABC ∂μ,
      P (join3 ABC.1 ABC.2.1 ABC.2.2) = NP (join3 ABC.1 ABC.2.1 ABC.2.2) ∧
      BQP (join3 ABC.1 ABC.2.1 ABC.2.2) = PSPACE (join3 ABC.1 ABC.2.1 ABC.2.2) ∧
      IP ABC.1 = PSPACE ABC.1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ f : List Bool → Bool,
        (∀ A : NUAlg, ∀ᶠ n in Filter.atTop,
          A.success (join3 ABC.1 ABC.2.1 ABC.2.2) f n ≤ 1 - δ) ∧
        {x | f x = true} ∈ PSPACE ABC.1 ∧ {x | f x = true} ∈ IP (join3 ABC.1 ABC.2.1 ABC.2.2) ∧
        PSPACE ABC.1 ⊆ IP (join3 ABC.1 ABC.2.1 ABC.2.2) := by sorry

end QAdvFew.PoQOracle
