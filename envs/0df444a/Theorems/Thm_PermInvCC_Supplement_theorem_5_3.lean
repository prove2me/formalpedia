-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_5_3
-- name    : PermInvCC.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:59:22.989204+00:00
-- url     : https://prove2.me/theorems/04e8e585-55d6-4a72-91a2-026a889b53f9
-- title:
--   Theorem 5.3 — XOR communication separation: $Q(F^\oplus_s)=O_\varepsilon(\log s)$, $R^{\mathrm{pub}}(F^\oplus_s)=\Omega_\varepsilon(s^{1-\varepsilon})$
-- statement:
--   Fix $\varepsilon \in (0,1)$. There are constants $C, c > 0$ depending only on $\varepsilon$ such that for infinitely many even $s$ there is a partial function $\psi : \{0,1\}^s \to \{-1,+1,*\}$ whose XOR communication problem $F^{\oplus}_s(A,B) = \psi(A \oplus B)$ satisfies
--
--   $$Q(F^{\oplus}_s) \le C \log s, \qquad R^{\mathrm{pub}}(F^{\oplus}_s) \ge c\, s^{1-\varepsilon},$$
--
--   that is, $Q(F^{\oplus}_s) = O_\varepsilon(\log s)$ and $R^{\mathrm{pub}}(F^{\oplus}_s) = \Omega_\varepsilon(s^{1-\varepsilon})$. Here $Q$ is quantum communication complexity without prior entanglement and logarithms are base two.
--
--   This XOR separation is the common source of the separations of Theorem 1.3 and Theorem 1.4.
--
--   Differences from the source:
--   - reading: "infinitely many even s" with O_ε(·), Ω_ε(·) → constants C, c > 0 chosen after ε only; for every N a size ≥ N carrying a function with Q ≤ C·log(size) and R^pub ≥ c·size^(exponent); reason: the standard reading of asymptotic bounds along an infinite family, with constants uniform over the family
--   - reading: explicit partial functions ψ → ∃ ψ; reason: "explicit" has no formal content
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 5.3, eq. (5.3), p.23 (PDF p.26); F⊕_s defined in eq. (5.2)

import Mathlib
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Supplement_Qcc
import Definitions.Def_PermInvCC_Supplement_xorLift

namespace PermInvCC

namespace Supplement

/-- **Theorem 5.3 (XOR Communication Separation)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.23). For every fixed
`ε ∈ (0, 1)`, there are infinitely many even `s` and explicit partial functions
`ψ : {0,1}^s → {−1, +1, ∗}` such that `Q(F⊕_s) = O_ε(log s)` and
`R^pub(F⊕_s) = Ω_ε(s^{1−ε})` (5.3), where `F⊕_s(A, B) = ψ(A ⊕ B)` (5.2).

**Formalization Note.** Constants `C, c > 0` are chosen after `ε` only and are uniform over
the infinite family: for every `N` there is an even `s ≥ N` and a `ψ` with
`Q(F⊕_s) ≤ C log s` and `R^pub(F⊕_s) ≥ c s^{1−ε}`. The communication problem is `xorLift ψ`, not
`ψ`. The word "explicit" has no formal content and is not formalized. `Q` is `Qcc` (no prior
entanglement). Logs are base two. -/
theorem theorem_5_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ Even s ∧
      ∃ ψ : (Fin s → Bool) → Option Bool,
        (Qcc (xorLift ψ) : ℝ) ≤ C * Real.logb 2 s ∧
          c * (s : ℝ) ^ (1 - ε) ≤ (Rpub (xorLift ψ) : ℝ) := by sorry

end Supplement

end PermInvCC
