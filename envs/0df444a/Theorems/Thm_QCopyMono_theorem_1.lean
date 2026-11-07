-- Prove2me | Theorems.Thm_QCopyMono_theorem_1
-- name    : QCopyMono.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:33.852186+00:00
-- url     : https://prove2.me/theorems/c2434e52-9b7c-4055-8272-fd7fa55132ca
-- title:
--   Theorem 1 — testing monotonicity from $O(\min\{n^{3/2}/\varepsilon^2,\,n/\varepsilon^3\}\log(1/\delta))$ copies of $|\psi_f\rangle$
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge1$, every $0<\varepsilon\le1/2$ and every $0<\delta<1/2$ there is a quantum algorithm that uses at most
--   $$
--   C\cdot\min\Big\{\frac{n^{3/2}}{\varepsilon^2},\ \frac n{\varepsilon^3}\Big\}\cdot\log\frac1\delta
--   $$
--   copies of the function state $|\psi_f\rangle=2^{-n/2}\sum_x|x,f(x)\rangle$ to decide, with success probability at least $1-\delta$, whether $f$ is monotone or $\varepsilon$-far from monotone.
--
--   This is the upper bound of the paper; with the matching lower bound (Theorem 2, not part of this mission) it determines the quantum copy complexity of monotonicity testing for $2^{-\sqrt n/200}\le\varepsilon\le1/128$.
--
--   **Formalization Note** The algorithm is a two-outcome joint measurement on $t$ copies, given by its accepting effect; it depends on $n,\varepsilon,\delta$ but not on $f$. $n^{3/2}$ is the real power and $\log$ the natural logarithm.
--
--   Differences from the source:
--   - reading: a quantum algorithm that uses at most t copies of |ψ_f⟩ (p.3: arbitrary measurements on multiple copies; p.6: an arbitrary joint measurement on |ψ_f⟩^{⊗t}) → an effect 0 ⪯ E ⪯ 1 on the t-copy register, accepting with probability ⟨ψ_f^{⊗t}|E|ψ_f^{⊗t}⟩, chosen before f; reason: every t-copy algorithm with a yes/no answer induces such an effect and every such effect is a two-outcome joint measurement; the paper counts copies only and claims no gate or time bound
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Theorem 1 (Upper bound), pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Theorem 1 (Upper bound), pp.3–4: for every
`n ≥ 1`, `0 < ε ≤ 1/2` and `0 < δ < 1/2` there is a quantum algorithm that uses at most
`O(min{n^{3/2}/ε², n/ε³} log(1/δ))` copies of `|ψ_f⟩` to decide, with success probability at
least `1 − δ`, whether `f` is monotone or `ε`-far from monotone.

**Formalization Note.** The `O(·)` is one absolute constant `C`, chosen before `n, ε, δ`. The
algorithm is a two-outcome joint measurement on `t` copies, given by its accepting effect `E`
(`0 ⪯ E ⪯ 1`), which depends on `(n, ε, δ)` and not on `f`; the paper counts copies only, so
no gate or time bound is asserted. `n^{3/2}` is the real power and `log` is natural. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ < 1 / 2 →
      ∃ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
        (t : ℝ) ≤ C * min ((n : ℝ) ^ (3 / 2 : ℝ) / ε ^ 2) ((n : ℝ) / ε ^ 3) * Real.log (1 / δ) ∧
          IsMonoTester ε δ t E := by sorry

end QCopyMono
