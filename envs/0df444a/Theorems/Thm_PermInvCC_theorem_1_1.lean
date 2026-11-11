-- Prove2me | Theorems.Thm_PermInvCC_theorem_1_1
-- name    : PermInvCC.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:53.584027+00:00
-- url     : https://prove2.me/theorems/5c2b8e7f-a2a6-49b6-8dce-b35f676f02ee
-- title:
--   Theorem 1.1 — fixed-alphabet simulation $R^{\mathrm{pub}}(f)\le C_q\,t\log(2+n/t)$, $t=\min\{n,Q^*(f)^2\}$
-- statement:
--   For each $q\ge2$ there is a constant $C_q>0$ such that for every $n\ge2$, every partial function
--   $$f:[q]^n\times[q]^n\to\{-1,+1,*\}$$
--   invariant under simultaneous coordinate permutations and satisfying $Q^*(f)\ge1$ obeys
--   $$R^{\mathrm{pub}}(f)\le C_q\,t\log(2+n/t),\qquad t:=\min\{n,Q^*(f)^2\}. \tag{1.1}$$
--
--   For permutation-invariant problems over a fixed alphabet, classical public-coin communication is at most quadratically larger than entanglement-assisted quantum communication, up to the factor $\log(2+n/t)$.
--
--   Differences from the source:
--   - generalization: R^pub with Bob producing the output → R^pub with the output determined by the transcript (both parties output); reason: the Lean complexity is at least the paper's, so the Lean bound implies the paper's; it remains true since both-party output costs at most one more bit, absorbed by C_q
--   - encoding: values −1, +1, ∗ and Q* with arbitrary prior entanglement → Option Bool (none = ∗) and the EntQProtocol model (arbitrary input-independent start state, local unitaries, Bob measures); reason: Lean representation of Definition 2.1
--   - encoding: logarithms base two → Real.logb 2; reason: Lean notation; same values
--   - reading: arbitrary prior entanglement → an arbitrary input-independent unit start state on finitely many qubits W (W unbounded); reason: the standard finite-dimensional model of entanglement-assisted communication, the one of [LS09] and [SS24, Thm 2.22] on which the paper builds its quantum bounds (App. B.3); the paper never uses an infinite-dimensional state
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.1, p.1 (restated p.21; proof pp.21–22)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Qstar

namespace PermInvCC

/-- **Theorem 1.1 (Fixed-Alphabet Simulation)** (Y. Huang and Z. Ye, *Quantum Advantage of
Permutation-Invariant Functions in Communication Complexity*, arXiv:2609.40116, held version
sha256 fe1797dd…, p.1; restated p.21). For each `q ≥ 2`, there is a constant `C_q > 0` such that
every partial function `f : [q]ⁿ × [q]ⁿ → {−1, +1, ∗}` invariant under simultaneous coordinate
permutations and satisfying `Q*(f) ≥ 1` obeys `R^pub(f) ≤ C_q t log(2 + n/t)` with
`t := min{n, Q*(f)²}` (1.1).

**Formalization Note.** `C_q` is chosen after `q` and before `n` and `f`; `n ≥ 2` is the paper's
standing assumption (p.1). `R^pub` is the public-coin complexity with transcript-determined output
(at most one bit more than Bob-only output, so the Lean bound implies the paper's); `Q*` is the
entanglement-assisted quantum complexity with an arbitrary input-independent start state, local
unitaries and Bob's measurement. Logs are base two. -/
theorem theorem_1_1 (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ f : PartialFn n q, IsPermInvariant f →
      1 ≤ Qstar f →
        let t : ℝ := min (n : ℝ) ((Qstar f : ℝ) ^ 2)
        (Rpub f : ℝ) ≤ C * t * Real.logb 2 (2 + n / t) := by sorry

end PermInvCC
