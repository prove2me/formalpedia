-- Prove2me | Theorems.Thm_QCopyMono_amplify
-- name    : QCopyMono.amplify
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:56.089209+00:00
-- url     : https://prove2.me/theorems/e6208a7f-66b8-4ca2-bc51-5e800e22ebe5
-- title:
--   Amplification — majority of $O(\log(1/\delta))$ repetitions reduces error $1/3$ to $\delta$
-- statement:
--   There is an absolute constant $C_0>0$ with the following property. Let $E$ be a monotonicity tester with parameters $(\varepsilon,1/3)$ on $t$ copies (it accepts monotone functions with probability at least $2/3$ and $\varepsilon$-far functions with probability at most $1/3$). Then for every $0<\delta<1/2$ there are $k\le C_0\log(1/\delta)$ and a monotonicity tester with parameters $(\varepsilon,\delta)$ on $k\,t$ copies.
--
--   In the paper this is the step "repeating the algorithm independently $O(\log(1/\delta))$ times and taking the majority outcome reduces the error probability to at most $\delta$", by Hoeffding's inequality; it is applied to both the Fourier tester and the path tester.
--
--   Differences from the source:
--   - reading: a quantum algorithm that uses at most t copies of |ψ_f⟩ (p.3: arbitrary measurements on multiple copies; p.6: an arbitrary joint measurement on |ψ_f⟩^{⊗t}) → an effect 0 ⪯ E ⪯ 1 on the t-copy register, accepting with probability ⟨ψ_f^{⊗t}|E|ψ_f^{⊗t}⟩, chosen before f; reason: every t-copy algorithm with a yes/no answer induces such an effect and every such effect is a two-outcome joint measurement; the paper counts copies only and claims no gate or time bound
--   - generalization: applied to the Fourier tester and to the path tester (error at most 1/3) → every tester with error at most 1/3, for every n, ε, t; reason: the argument uses only the error bound; the two testers are instances
--   - encoding: k independent runs on fresh copies → an effect on k·t copies indexed by Fin (k * t); reason: the block layout of the copies is not fixed by the statement; same claim
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), proof of Proposition 1, p.10; §3.2.3, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), proof of Proposition 1, p.10, and §3.2.3,
p.16: "repeating the algorithm independently `O(log(1/δ))` times and taking the majority outcome
reduces the error probability to at most `δ`". There is an absolute `C₀ > 0` such that every
tester on `t` copies with error at most `1/3` yields, for each `0 < δ < 1/2`, a tester on `k·t`
copies with error at most `δ`, for some `k ≤ C₀ log(1/δ)`.

**Formalization Note.** The `k` runs act on disjoint blocks of the `k·t` copies; the copies are
indexed by `Fin (k * t)`, and the statement does not fix which positions form a block. `log` is
natural. -/
theorem amplify :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n t : ℕ) (ε : ℝ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
      IsMonoTester ε (1 / 3) t E → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ k : ℕ, (k : ℝ) ≤ C₀ * Real.log (1 / δ) ∧
          ∃ E' : Matrix (Fin (k * t) → X n) (Fin (k * t) → X n) ℂ,
            IsMonoTester ε δ (k * t) E' := by sorry

end QCopyMono
