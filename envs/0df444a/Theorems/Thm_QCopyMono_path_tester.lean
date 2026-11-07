-- Prove2me | Theorems.Thm_QCopyMono_path_tester
-- name    : QCopyMono.path_tester
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:38.102233+00:00
-- url     : https://prove2.me/theorems/c880f1e6-4bbf-454f-a07d-a1608fcfdc89
-- title:
--   §3.2.3 — path tester with $O((n/\varepsilon^3)\log(1/\delta))$ copies for $\varepsilon\ge n^{-1/2}$
-- statement:
--   There are absolute constants $n_0$ and $C>0$ such that for every $n\ge n_0$, every $n^{-1/2}\le\varepsilon\le1/2$ and every $0<\delta<1/2$ there is a quantum algorithm using at most
--   $$
--   C\,\frac n{\varepsilon^3}\log\frac1\delta
--   $$
--   copies of $|\psi_f\rangle$ that decides, with success probability at least $1-\delta$, whether $f$ is monotone or $\varepsilon$-far from monotone.
--
--   This is the paper's second tester, combining the coarse influence filter, the path observables $Q_d$ and $H_d\otimes Z$ at every scale $d$, a median over repetitions, and majority amplification. It gives the $n/\varepsilon^3$ branch of Theorem 1.
--
--   Differences from the source:
--   - reading: a quantum algorithm that uses at most t copies of |ψ_f⟩ (p.3: arbitrary measurements on multiple copies; p.6: an arbitrary joint measurement on |ψ_f⟩^{⊗t}) → an effect 0 ⪯ E ⪯ 1 on the t-copy register, accepting with probability ⟨ψ_f^{⊗t}|E|ψ_f^{⊗t}⟩, chosen before f; reason: every t-copy algorithm with a yes/no answer induces such an effect and every such effect is a two-outcome joint measurement; the paper counts copies only and claims no gate or time bound
--   - reading: n ≥ n_0 for the constant n_0 of §3.2 → n ≥ n_0 for some absolute n_0 ∈ ℕ chosen before n, ε, δ; reason: n_0 is the unspecified absolute constant of Lemmas 6–7, increased if necessary in their proofs (p.36, p.40); the claim is that such a constant exists
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2.3, pp.15–16 (the tester of §3.2, p.10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2.3, pp.15–16 (the path tester of §3.2,
p.10): assuming `n^{−1/2} ≤ ε ≤ 1/2` and `n ≥ n₀`, monotonicity can be tested with error at
most `δ`, `0 < δ < 1/2`, from `O((n/ε³) log(1/δ))` copies of `|ψ_f⟩`.

**Formalization Note.** `n₀` and `C` are absolute and chosen before `n, ε, δ`; the effect
depends on `(n, ε, δ)` only, never on `f`. `log` is natural. -/
theorem path_tester :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ε δ : ℝ,
      (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ε → ε ≤ 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∃ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
          (t : ℝ) ≤ C * ((n : ℝ) / ε ^ 3 * Real.log (1 / δ)) ∧ IsMonoTester ε δ t E := by sorry

end QCopyMono
