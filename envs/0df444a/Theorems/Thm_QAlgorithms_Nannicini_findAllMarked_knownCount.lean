-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_findAllMarked_knownCount
-- name    : QAlgorithms.Nannicini.findAllMarked_knownCount
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:41.784215+00:00
-- url     : https://prove2.me/theorems/2935d96c-3f4e-4f46-812a-e4c593a8b720
-- title:
--   Finding all marked elements with O(√(|M| 2^n)) oracle calls
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be accessed through $U_f:|j\rangle|y\rangle\mapsto|j\rangle|y\oplus f(j)\rangle$ and let $M=\{j: f(j)=1\}$ be the set of marked elements. There is an absolute constant $C>0$ such that for every $n$ and every known value $t$ there is a quantum query algorithm making $T$ queries to $U_f$, with
--
--   $$T\le C\sqrt{t\,2^n},$$
--
--   whose output is a subset of $\{0,1\}^n$ and which, for every $f$ with exactly $t$ marked elements, outputs exactly the set $M$ with probability at least $2/3$.
--
--   As in Corollary 4.9, the algorithm is a fixed initial state followed by $f$-independent unitaries interleaved with $T$ applications of $U_f\otimes I$, then a measurement in the computational basis and a fixed output map; it may depend on $n$ and $t$ but not on $f$.
--
--   The source obtains this by repeatedly finding a marked element and unmarking it; the total cost is the sum $\sum_{k}\sqrt{2^n/(t-k)}=O(\sqrt{t2^n})$.
--
--   **Formalization Note** The success probability is not printed; $2/3$ is the bounded-error convention. The adaptive procedure (measure, unmark, repeat) is represented by a single query algorithm with deferred measurements and the same query count. The case $t=0$ is included: then $T=0$ and the algorithm outputs the empty set.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 80, Corollary 4.10. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini p.80, Corollary 4.10: let `M = {j ∈ {0,1}^n : f(j) = 1}` be the set of marked
elements, with `|M|` known. Then all elements of `M` can be determined using `O(√(|M| 2^n))`
applications of `f` (through `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩`). Formally: there is a constant `C > 0`
such that for all `n` and every known count `t` there is a `T`-query algorithm with an output map
to subsets of `{0,1}^n`, with `T ≤ C √(t 2^n)`, which for every `f` with exactly `t` marked
elements outputs the set `M` with probability at least `2/3` (bounded-error convention). -/
theorem findAllMarked_knownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ,
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Finset (Qubits n)),
        (T : ℝ) ≤ C * Real.sqrt ((t : ℝ) * (2 : ℝ) ^ n) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f))
            fun z => out z = Finset.univ.filter fun j => f j = true := by
  sorry



end QAlgorithms.Nannicini
