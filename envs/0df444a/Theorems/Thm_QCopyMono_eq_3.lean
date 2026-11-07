-- Prove2me | Theorems.Thm_QCopyMono_eq_3
-- name    : QCopyMono.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:01.779679+00:00
-- url     : https://prove2.me/theorems/58aba393-e703-4b89-b18e-b2b7a0c992c2
-- title:
--   Eq. (3) — edge-tester bound: $f\in\mathrm{MON}_n\Rightarrow p=0$, $\varepsilon$-far $\Rightarrow p\ge\varepsilon/n$
-- statement:
--   Let $n\ge1$. For every Boolean function $f$ on $\{0,1\}^n$:
--
--   1. if $f$ is monotone, then $p=0$;
--   2. if $\mathrm{dist}(f,\mathrm{MON}_n)\ge\varepsilon$, then $p\ge\varepsilon/n$.
--
--   Here $p$ is the probability that a uniformly random edge of the hypercube violates monotonicity. This is the classical edge-tester bound (cited to [Gol+00]); it separates monotone from far functions by the value of $p$.
--
--   Differences from the source:
--   - generalization: ε the distance parameter of the testing problem (ε > 0) → every real ε; reason: for ε ≤ 0 the clause follows from p ≥ 0, so the statement specializes to the printed one
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.1, p.7, eq. (3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Influence

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.1, p.7, eq. (3) (the classical edge-tester
bound, cited to [Gol+00]): for `n ≥ 1`, `f ∈ MONₙ ⟹ p = 0` and
`dist(f, MONₙ) ≥ ε ⟹ p ≥ ε/n`.

**Formalization Note.** `ε` is any real number (for `ε ≤ 0` the second clause is immediate
from `p ≥ 0`; for `ε > 1/2` no function is `ε`-far). -/
theorem eq_3 (n : ℕ) (hn : 1 ≤ n) :
    (∀ f : Qubits n → Bool, Monotone f → edgeViolProb f = 0) ∧
      ∀ (ε : ℝ) (f : Qubits n → Bool), IsFar ε f → ε / n ≤ edgeViolProb f := by sorry

end QCopyMono
