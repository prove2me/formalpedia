-- Prove2me | Theorems.Thm_QIndInf_reference_domination
-- name    : QIndInf.reference_domination
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:42.488051+00:00
-- url     : https://prove2.me/theorems/fe6d149c-588c-4790-84cf-dffb73f6b6f3
-- title:
--   Eq. (58) — domination of every short-program source by the reference state
-- statement:
--   There is a constant $c\in\mathbb N$ with the following property. For every source model $T\mapsto\rho^{T}$ and all $n,s,t\in\mathbb N$, let $\mu$ be the reference state, the uniform mixture of the sources of all programs of length at most $s$. Then:
--
--   1. each $\mu_{R_1\dots R_m}$ is a density operator;
--   2. $\mathrm{Tr}_{R_{m+1}}\mu_{R_1\dots R_{m+1}}=\mu_{R_1\dots R_m}$ for every $m$;
--   3. for every program $T$ with $|T|\le s$ and every $m$,
--
--   $$
--   \mu_{R_1\dots R_m}\ \ge\ 2^{-cs}\,\rho^{T}_{R_1\dots R_m}.
--   $$
--
--   Here $A\ge B$ means that $A-B$ is positive semidefinite (p.15). This is the domination step (58) of the proof of Theorem 4.2: a single reference, independent of the unknown program and of $m$, gives every admissible source weight at least $2^{-cs}$. The constant is uniform in the source model, $n$, $t$, $s$ and $m$.
--
--   Differences from the source:
--   - generalization: Lemma 3.6 / Eq. (58): for the Turing-machine source model, the universal density matrix μ^{U,p(s,t)} (programs of length p(s,t) on a universal machine U) satisfies μ ≥ 2^{−cs} ρ → for every source model, the uniform mixture over programs of length ≤ s is a consistent family of states with μ ≥ 2^{−cs} ρ^T for all |T| ≤ s, with c ∈ ℕ uniform in the model; reason: the proof of Theorem 4.2 uses only a reference that depends on (n, s, t) alone, is consistent across m and dominates every admissible source (paper.md R2); instantiating the model with the paper's encoding gives such a reference, while Turing machines and universal simulation are not formalized
--   - encoding: A ≥ B (p.15); constant c > 0 → (A − B).PosSemidef; c a natural number; reason: same order relation; a natural constant is a positive real constant unless c = 0, and c = 0 would only make the claim stronger
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (58), p.20, from Lemma 3.6, Eq. (41), p.17; consistency of the reference: remark after Eq. (40), p.16

import Mathlib
import Definitions.Def_QIndInf_refState

set_option autoImplicit false

open scoped ComplexOrder

namespace QIndInf

/-- **Domination by the reference state (Eq. (58) via Lemma 3.6, for every source model).**
There is a constant `c` such that for every source model `gen` and all `n, s, t`, the reference
family `μ = refState gen n s t` (the uniform mixture of the sources of all programs of length at
most `s`) is a quantum source (each `μ_{R₁…R_m}` is a density operator, consistent under tracing
out the last register), and for every program `T` with `|T| ≤ s` and every `m`,
`μ_{R₁…R_m} ≥ 2^{−cs} ρ^T_{R₁…R_m}`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (58), p.20, from Lemma 3.6, Eq. (41), p.17; the
consistency of the reference across `m` is the remark after Eq. (40), p.16.

**Formalization Note.** `A ≥ B` is `(A − B).PosSemidef` (p.15). The constant `c` is a natural
number, quantified before the source model, so it does not depend on `gen`, `n`, `t`, `s` or `m`.
The bound is stated for the reference family of this development (programs of length `≤ s` run in
the source model) instead of the paper's `μ^{U,p(s,t)}` (programs of length `p(s,t)` run on a
universal machine). -/
theorem reference_domination :
    ∃ c : ℕ, ∀ (gen : SourceModel) (n s t : ℕ),
      (∀ m, WildeQIT.IsDensityOperator (refState gen n s t m)) ∧
      (∀ m, traceLast (refState gen n s t (m + 1)) = refState gen n s t m) ∧
      (∀ T : List Bool, T.length ≤ s → ∀ m,
        (refState gen n s t m - ((2 : ℂ) ^ (c * s))⁻¹ • (gen n t T).state m).PosSemidef) := by sorry

end QIndInf
