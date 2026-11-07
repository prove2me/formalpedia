-- Prove2me | Theorems.Thm_QCopyMono_proposition_1
-- name    : QCopyMono.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:45.117821+00:00
-- url     : https://prove2.me/theorems/d8765514-f69d-43c9-adb8-ebeca1046a2a
-- title:
--   Proposition 1 — Fourier tester with $O(n^{3/2}\log(1/\delta)/\varepsilon^2)$ copies
-- statement:
--   There is an absolute constant $C>0$ such that for every $n$, every $\varepsilon>0$ and every $0<\delta<1/2$ there is a quantum algorithm using at most
--   $$
--   C\,\frac{n^{3/2}\log(1/\delta)}{\varepsilon^2}
--   $$
--   copies of $|\psi_f\rangle$ that distinguishes monotone functions from functions that are $\varepsilon$-far from monotone with probability at least $1-\delta$.
--
--   This is the paper's first tester: a coarse Fourier estimate of the influence filters out high-influence functions, after which the edge-violation probability $p$ is estimated from Fourier and computational-basis samples. It gives the $n^{3/2}/\varepsilon^2$ branch of Theorem 1.
--
--   Differences from the source:
--   - reading: a quantum algorithm that uses at most t copies of |ψ_f⟩ (p.3: arbitrary measurements on multiple copies; p.6: an arbitrary joint measurement on |ψ_f⟩^{⊗t}) → an effect 0 ⪯ E ⪯ 1 on the t-copy register, accepting with probability ⟨ψ_f^{⊗t}|E|ψ_f^{⊗t}⟩, chosen before f; reason: every t-copy algorithm with a yes/no answer induces such an effect and every such effect is a two-outcome joint measurement; the paper counts copies only and claims no gate or time bound
--   - reading: ε with no printed range (§1: a parameter ε > 0) → every ε > 0; reason: the printed domain; for ε > 1/2 no function is ε-far and the statement is still true
--   - generalization: n ≥ 1 (standing) → every n ∈ ℕ; reason: at n = 0 no function is ε-far for ε > 0, so the case is true and the statement specializes to n ≥ 1
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Proposition 1, p.7 (proof pp.7–10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Proposition 1, p.7: there is a quantum
algorithm that, given `O(n^{3/2} log(1/δ)/ε²)` copies of `|ψ_f⟩`, distinguishes monotone
functions from functions that are `ε`-far from monotone with probability at least `1 − δ`, for
`0 < δ < 1/2`.

**Formalization Note.** One absolute constant `C` is chosen before `n, ε, δ`; the effect `E`
depends on `(n, ε, δ)` only, never on `f`. `ε > 0` is the printed (unrestricted) domain, and
every `n` is allowed. `log` is natural. -/
theorem proposition_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 / 2 →
      ∃ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
        (t : ℝ) ≤ C * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log (1 / δ) / ε ^ 2) ∧
          IsMonoTester ε δ t E := by sorry

end QCopyMono
