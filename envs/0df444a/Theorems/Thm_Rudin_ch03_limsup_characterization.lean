-- Prove2me | Theorems.Thm_Rudin_ch03_limsup_characterization
-- name    : Rudin.ch03_limsup_characterization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:00:43.409987+00:00
-- url     : https://prove2.me/theorems/e3e7d7fa-46a4-429c-9162-bab765a194a5
-- title:
--   Theorem 3.17 — characterization of the upper limit
-- statement:
--   Let $\{s_n\}$ be a sequence of real numbers and let $s^{*}$ be its upper limit in $[-\infty, +\infty]$. Then (a) $s^{*}$ is a subsequential limit of $\{s_n\}$, and (b) if $x > s^{*}$ then there is an $N$ with $s_n < x$ for all $n \ge N$. Moreover $s^{*}$ is the only extended real number with properties (a) and (b).
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 54, Definition 3.16 and Theorem 3.17

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.17: let `s` be a sequence of real numbers and let `s*` be its upper limit
in the extended real number system.  Then (a) `s*` is a subsequential limit of `s`, and (b) if
`x > s*` then `s n < x` for all large `n`; moreover `s*` is the only extended real number with
these two properties. -/
theorem ch03_limsup_characterization (s : ℕ → ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => ((s (φ k) : ℝ) : EReal)) atTop
          (𝓝 (limsup (fun n => ((s n : ℝ) : EReal)) atTop))) ∧
    (∀ x : EReal, limsup (fun n => ((s n : ℝ) : EReal)) atTop < x →
        ∃ N, ∀ n ≥ N, ((s n : ℝ) : EReal) < x) ∧
    (∀ y : EReal,
        ((∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => ((s (φ k) : ℝ) : EReal)) atTop (𝓝 y)) ∧
          (∀ x : EReal, y < x → ∃ N, ∀ n ≥ N, ((s n : ℝ) : EReal) < x)) →
        y = limsup (fun n => ((s n : ℝ) : EReal)) atTop) := by sorry

end Rudin
