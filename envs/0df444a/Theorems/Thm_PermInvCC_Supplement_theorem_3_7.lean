-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_3_7
-- name    : PermInvCC.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:57:54.10395+00:00
-- url     : https://prove2.me/theorems/db738b0a-575d-42e4-aed1-795720d42c43
-- title:
--   Theorem 3.7 — quantum upper bound: $Q(f_{\rho,\sigma})\le C_q\min\{n,h_{f_{\rho,\sigma}}^{-1}\log n\}$
-- statement:
--   Fix $q \ge 2$. There is a constant $C_q > 0$ such that for every $n \ge 2$, every permutation-invariant partial function $f : [q]^n \times [q]^n \to \{-1,+1,*\}$, and every pair of histograms $\rho, \sigma$ of total $n$, the fixed-margin restriction $g := f_{\rho,\sigma}$ satisfies
--
--   $$Q(g) \le C_q \min\{n,\ h_g^{-1}\log n\},$$
--
--   where $Q$ is quantum communication complexity without prior entanglement, $h_g$ is the separation parameter of Definition 2.4 ($h_g = 1$ if at most one label is promised), and logarithms are base two.
--
--   Compared with the classical bound of Theorem 3.1, which is quadratic in $h_g^{-1}$, the quantum bound is linear in $h_g^{-1}$; it is the upper half of Theorem 1.2.
--
--   **Formalization Note** $C_q$ is chosen after $q$ and before $n$, $f$, $\rho$, $\sigma$; $g$ is written as the restriction of $f$ to the histograms $\rho, \sigma$.
--
--   Differences from the source:
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
--   - encoding: We take n ≥ 2 (p.1) → hypothesis 2 ≤ n; reason: the paper's standing assumption
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 3.7, eq. (3.1), p.15 (PDF p.18); restated p.35 (PDF p.38)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_Supplement_Qcc
import Definitions.Def_PermInvCC_Supplement_restrict

namespace PermInvCC

namespace Supplement

/-- **Theorem 3.7 (Quantum Upper Bound)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.15; restated p.35). For every fixed
`q ≥ 2`, there is a constant `C_q > 0` such that every fixed-margin restriction `g := f_{ρ,σ}`
of a permutation-invariant partial function `f : [q]ⁿ × [q]ⁿ → {−1, +1, ∗}` satisfies
`Q(g) ≤ C_q min{n, h_g^{-1} log n}` (3.1).

**Formalization Note.** `C_q` is chosen after `q` and before `n`, `f`, `ρ`, `σ`; `n ≥ 2`
is the paper's standing assumption. `ρ, σ` range over all histograms of total `n`; `g` is
`restrict f ρ σ`, `Q` is `Qcc` (no prior entanglement) and `h_g` the base `hg` (`= 1` when no
oppositely labelled pair is promised). Logs are base two. -/
theorem theorem_3_7 (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ f : PartialFn n q, IsPermInvariant f →
      ∀ ρ σ : Fin q → ℕ, ∑ a, ρ a = n → ∑ b, σ b = n →
        (Qcc (restrict f ρ σ) : ℝ) ≤
          C * min (n : ℝ) ((hg (restrict f ρ σ))⁻¹ * Real.logb 2 n) := by sorry

end Supplement

end PermInvCC
