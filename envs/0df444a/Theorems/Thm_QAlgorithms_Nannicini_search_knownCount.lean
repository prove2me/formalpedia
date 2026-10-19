-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_search_knownCount
-- name    : QAlgorithms.Nannicini.search_knownCount
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:45:31.586372+00:00
-- url     : https://prove2.me/theorems/b405e490-ffcc-479a-9403-cbc510a1bb92
-- title:
--   Search with a known number of marked elements in O(√(2^n/|M|)) oracle calls
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be accessed through the oracle $U_f:|j\rangle|y\rangle\mapsto|j\rangle|y\oplus f(j)\rangle$, queried in superposition, and let $M=\{j: f(j)=1\}$. There is an absolute constant $C>0$ such that for every $n$ and every known value $t$ with $1\le t\le 2^n$ there is a quantum query algorithm making $T$ queries to $U_f$, with
--
--   $$T\le C\sqrt{\frac{2^n}{t}},$$
--
--   which, for every $f$ with exactly $t$ marked elements, outputs an element of $M$ with probability at least $2/3$.
--
--   A $T$-query algorithm is a fixed initial state on the query register (the $n$ index qubits and one target qubit) together with a finite workspace, followed by $U_T(U_f\otimes I)U_{T-1}\cdots(U_f\otimes I)U_0$, where the unitaries $U_i$ do not depend on $f$; the output is a fixed function of the measured basis state. The algorithm may depend on $n$ and on $t$ (the count is known), but not on $f$.
--
--   This is Grover search with several marked items, a direct consequence of amplitude amplification.
--
--   **Formalization Note** The source prints no success probability; $2/3$ is the bounded-error convention of Rem. 4.7, which can be boosted by repetition. Intermediate measurements are deferred, so a single unitary query algorithm represents the procedure with the same query count. A constant valid for all $n$ and $t$ is equivalent to the threshold form of $O(\cdot)$, because $T\le 2^n$ queries always suffice on the finitely many small $n$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 79, Corollary 4.9. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.79, Corollary 4.9: let `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` implement a Boolean
function `f : {0,1}^n → {0,1}` and let `M = {j : f(j) = 1}`. If `|M|` is known, an element of `M`
can be determined with `O(√(2^n/|M|))` applications of `U_f`. Formally: there is a constant `C > 0`
such that for all `n` and every known count `1 ≤ t ≤ 2^n` there is a `T`-query algorithm (fixed
input-independent unitaries on the query register and a workspace with basis `Fin w`,
interleaved with `T` applications of `U_f`) and an output map, with `T ≤ C √(2^n/t)`,
which for every `f` with exactly `t` marked elements outputs a marked element with probability at
least `2/3` (the bounded-error convention, Rem. 4.7). -/
theorem search_knownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ, 1 ≤ t → t ≤ 2 ^ n →
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Qubits n),
        (T : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ n / (t : ℝ)) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f)) fun z => f (out z) = true := by
  sorry




end QAlgorithms.Nannicini
