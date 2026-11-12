-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_parallel_block_commitment
-- name    : SuccinctArgOWF.Kilian.parallel_block_commitment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:13.026662+00:00
-- url     : https://prove2.me/theorems/e1eedd07-965c-45d5-b777-fe3916865def
-- title:
--   Theorem 6.2 — parallel blocks with shared receiver coins
-- statement:
--   Let $\widetilde{\mathrm{Com}}$ be an $\ell$-round public-coin commitment scheme for $n$-bit messages, $n\ge1$, let $N$ be a multiple of $n$, and let $\mathrm{Com}$ be the scheme of Construction 6.1. Then, for one universal constant $C$:
--
--   1. $\mathrm{Com}$ is an $\ell$-round public-coin commitment scheme with interval opening for messages in $\{0,1\}^N$, complete when $\widetilde{\mathrm{Com}}$ is;
--   2. for all $t,L\in\mathbb N$, every adversary of running time $t$ that outputs an interval of size at most $L$ wins the selective interval binding game of $\mathrm{Com}$ with probability at most
--
--   $$\Bigl(\Bigl\lceil\frac{L}{n}\Bigr\rceil+1\Bigr)\cdot\mathrm{bind}_{\widetilde{\mathrm{Com}}}(C\,t);$$
--
--   3. if the committer of $\widetilde{\mathrm{Com}}$ sends $\tilde d$ bits in every round, the sender messages of $\mathrm{Com}$ lie in $\{0,1\}^{N\tilde d/n}$ and $\mathrm{Com}$ has local verification (Definition 5.1) with respect to $J(I)=\{(a-1)\tilde d+1,\dots,b\tilde d\}$, where $B(I)=\{a,\dots,b\}$.
--
--   This turns a plain commitment into the inner scheme with interval openings and local verification needed by the composition theorem.
--
--   Differences from the source:
--   - reading: C̃om for n-bit messages, N a multiple of n → additionally 0 < n; reason: the blocks [N/n] of Construction 6.1 require n ≥ 1
--   - encoding: bind_C̃om(O(t)) → bind_C̃om(C·t) with one constant C chosen before C̃om, N, t, L and the adversary; reason: the O-constant is universal
--   - generalization: C̃om is a commitment scheme (complete) → completeness of C̃om is assumed only for the completeness clause; reason: the binding and local-verification clauses do not use it
--   - encoding: an adversary that outputs an interval of size at most L → whenever its first output is an interval of [N], that interval has at most L positions; reason: an output that is not an interval loses the game
--   - encoding: round message y_j = (y_j^{(i)})_{i ∈ [N/n]} → the concatenation when all block messages have equal length, otherwise a self-delimiting code of the tuple; reason: both are unambiguous encodings of the tuple; the first is the paper's {0,1}^{Nd̃/n} form
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Theorem 6.2, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Blocks

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Theorem 6.2, Dujmovic–Wichs p.19. For an `ℓ`-round public-coin commitment `C̃om` for `n`-bit
messages and `N` a multiple of `n`, Construction 6.1 is complete (when `C̃om` is), every adversary of
running time `t` that outputs an interval of size at most `L` wins its selective interval binding game
with probability at most `(⌈L/n⌉ + 1) · bind_{C̃om}(C·t)` for a universal constant `C`, and if `C̃om`
sends `d̃` bits in every round then the sender messages lie in `{0,1}^{N d̃/n}` and it has local
verification with respect to `J(I) = {(a−1)d̃+1, …, b d̃}`, `B(I) = {a, …, b}`. -/
theorem parallel_block_commitment :
    ∃ C : ℕ, ∀ (Ct : Commit) (N : ℕ), 0 < Ct.n → Ct.n ∣ N →
      (Ct.Complete → (constr61 Ct N).Complete) ∧
      (∀ (t L : ℕ) (A : Adv), A.RunsWithin t [] (Set.range (constr61 Ct N).selSched) →
        (constr61 Ct N).SelSizeLe A t L →
        (constr61 Ct N).selProb false A t ≤
          (((L + Ct.n - 1) / Ct.n + 1 : ℕ) : ℝ) * Ct.bind (C * t)) ∧
      (∀ dt : ℕ, Ct.MsgLen dt →
        (constr61 Ct N).MsgLen (N * dt / Ct.n) ∧
          (constr61 Ct N).LocalVer (N * dt / Ct.n) (blockJ Ct.n dt)) := by sorry

end SuccinctArgOWF.Kilian
