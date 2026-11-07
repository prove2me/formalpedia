-- Prove2me | Theorems.Thm_QLocalCert_lemma_27
-- name    : QLocalCert.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:25.677204+00:00
-- url     : https://prove2.me/theorems/9574cc6c-4b62-457d-93aa-30080fe3b5ef
-- title:
--   Lemma 27 — $\mathrm{Tree}_\mu$ has a deterministic one-round dMA certification with $O(\log n)$ bits
-- statement:
--   There is a constant $C$ such that for every $\mu\ge1$, every $n\ge1$ and every identifier bound $U\ge n$ there is a deterministic one-round dMA protocol on $n$-node networks that decides $\mathrm{Tree}_\mu$ with completeness $1$ and soundness error $0$ on every instance (every connected graph, identifier and port assignment), using certificates of at most $b\le C\log_2n$ bits per node, and whose messages, encoded injectively as bit strings, have at most $C\log_2n$ bits each, on every instance and for every admissible certificate assignment.
--
--   This structural certification is the classical half of the quantum protocol of Lemma 28: after one round the two roots know their strings, and the shape of the tree is certified.
--
--   Differences from the source:
--   - encoding: O(log n) certificate bits per node and bits per message → b ≤ C log₂ n and every encoded message ≤ C log₂ n bits, for n ≥ 1, U ≥ n; reason: big-O as one constant
--   - generalization: O(log n) for the fixed constant µ (the implicit constant may depend on µ) → one constant C chosen before µ; reason: the name ranges are bounded by ρ < n on every size passing (V1), p.40; specializes to each fixed µ
--   - encoding: deterministic protocol (completeness/soundness not printed) → IsDeterministic, completeness 1 and soundness error 0; reason: a deterministic protocol accepts with probability 0 or 1, so certification means exactly (1, 0)
--   - generalization: identifier bound U = n^{O(1)} → every U ≥ n; reason: the certificates carry no identifiers; specializes to every polynomial bound U ≥ n
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 27 and its proof, pp.37–40

import Mathlib
import Definitions.Def_QLocalCert_DMA
import Definitions.Def_QLocalCert_TreeEQ

set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 27** (p.37). "The property Treeµ admits a deterministic one-round dMA protocol on
connected n-vertex graphs, using O(log n) certificate bits per node and bits per message."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 27 and its proof, pp.37–40 (Complexity, p.40: "The fixed field bounds N̂ ≤ n,
all name ranges in Table 2, and ρ < n on any size passing (V1) give O(log n) bits per node and per
message on every instance, including no-instances").

**Formalization Note.**
* One constant `C` before `µ` (justified on p.40 by `ρ < n`) and before `n ≥ 1`, `U ≥ n`.
* The protocol is a one-round dMA protocol (`DMA n U 1`) that is deterministic, uses
  certificates of at most `b ≤ C log₂ n` bits, and decides `Treeµ` with completeness 1 and
  soundness error 0, on every instance (every identifier and port assignment).
* "Bits per message": messages are encoded injectively as bit strings `enc`, and every message
  sent in the round, on every instance and for every admissible certificate assignment, has at
  most `C log₂ n` bits. -/
theorem lemma_27 :
    ∃ C : ℝ, ∀ μ : ℕ, 1 ≤ μ → ∀ n : ℕ, 1 ≤ n → ∀ U : ℕ, n ≤ U →
      ∃ (P : DMA n U 1) (b : ℕ) (enc : P.Msg → List Bool),
        P.IsDeterministic ∧ (b : ℝ) ≤ C * Real.logb 2 n ∧ Function.Injective enc ∧
        (∀ (I : Instance n U) (Γ : Fin n → List Bool) (ω : Fin n → P.PrivRand) (ϱ : P.PubRand)
            (v : Fin n) (p : Fin (I.deg v)), (∀ u, (Γ u).length ≤ b) →
          ((enc (P.send (P.state I Γ ω ϱ 0 v) (I.deg v) p)).length : ℝ) ≤ C * Real.logb 2 n) ∧
        P.Correct (TreeP μ) b 1 0 := by sorry

end QLocalCert
