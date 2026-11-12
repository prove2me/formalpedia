-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_3_10
-- name    : QuantumKtSoI.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:27.998206+00:00
-- url     : https://prove2.me/theorems/5793a146-d962-4b0a-90c8-6250ef9f4706
-- title:
--   Lemma 3.10 — repetition with a majority vote
-- statement:
--   There is a constant $c_1\ge1$ such that the following holds. Let $e$ be a description, $x$ a string, $t\ge1$ a real deadline and $r\ge1$ an integer; put $T=c_1r^2(t+|x|+1)$. For every $w$, if $X$ is the sum of $r$ independent $\{0,1\}$-valued variables, each equal to $1$ with probability $p=P_e(x;t,w)$, then
--   $$P_{\mathrm{AMP}(r,e)}(x;T,w)\ \ge\ \Pr[X>r/2]=\sum_{k\le r,\ 2k>r}\binom rk p^k(1-p)^{r-k}.$$
--   If moreover $M(e)$ halts within $t$ steps on $x$, then $M(\mathrm{AMP}(r,e))$ halts within $T$ steps on $x$.
--
--   Repetition amplifies a witness's success probability at a quadratic cost in $r$ in the running time; it underlies the amplification lemma and subadditivity.
--
--   Differences from the source:
--   - generalization: a constant c₁ for the paper's fixed glue routines → one constant c₁ chosen before the glue routines, serving every admissible routine set; reason: M(AMP(r,e)) runs no glue routine of its own; the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: Pr[X > r/2] for a sum X of r independent bits → the binomial tail Σ_{k ≤ r, 2k > r} C(r,k) pᵏ(1−p)^{r−k}; reason: the distribution of such a sum is binomial
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 3.10, p.28

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 3.10** (Repetition; Myrisiotis, STOC 2027 submission, held version sha256 6616571c…,
p.28). There is a constant `c₁ ≥ 1` such that the following holds. Let `e ∈ E`, `x ∈ {0,1}*`, let
`t ≥ 1` be a real deadline, and let `r ≥ 1` be an integer; put `T = c₁ r² (t + |x| + 1)`. For
every `w`, if `X` is the sum of `r` independent random variables with values in `{0,1}`, each
equal to `1` with probability `P_e(x;t,w)`, then `P_{AMP(r,e)}(x;T,w) ≥ Pr[X > r/2]`. If moreover
`M(e)` halts within `t` steps on `x`, then `M(AMP(r,e))` halts within `T` steps on `x`.

**Formalization Note** `Pr[X > r/2]` is the binomial tail `Σ_{k ≤ r, 2k > r} C(r,k) pᵏ (1−p)^{r−k}`
with `p = P_e(x;t,w)`. The constant `c₁` is chosen before the glue routines and serves every
admissible routine set: `M(AMP(r,e))` runs no glue routine of its own, and its loading, comparison
and copy routines are pinned (see `ampCore`). -/
theorem lemma_3_10 :
    ∃ c₁ : ℝ, 1 ≤ c₁ ∧ ∀ G : GlueRoutines, G.Admissible →
      ∀ (e : Desc) (x : List Bool) (t : ℝ), 1 ≤ t →
      ∀ r : ℕ+,
        let T : ℝ := c₁ * (r : ℝ) ^ 2 * (t + x.length + 1)
        (∀ w : List Bool,
            ∑ k ∈ (Finset.range ((r : ℕ) + 1)).filter (fun k => (r : ℕ) < 2 * k),
                ((r : ℕ).choose k : ℝ) * (e.probR G x t w) ^ k * (1 - e.probR G x t w) ^ ((r : ℕ) - k) ≤
              (Desc.amp r e).probR G x T w) ∧
          ((e.machine G).HaltsWithin x ⌊t⌋₊ → ((Desc.amp r e).machine G).HaltsWithin x ⌊T⌋₊) := by sorry

end QuantumKtSoI
