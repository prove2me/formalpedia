-- Prove2me | Theorems.Thm_PermInvCC_lemma_4_4
-- name    : PermInvCC.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:20.827312+00:00
-- url     : https://prove2.me/theorems/5dcd035d-3a29-40fb-a999-f4b5ee23c818
-- title:
--   Lemma 4.4 — quantum lower bound $c+1\ge b_q\sqrt{(B+g)\Lambda}/g$ for an alternating cycle
-- statement:
--   For each $q\ge2$ there is a constant $b_q>0$ such that the following holds. Let $S_1,S_2$ be types of total $N$ that differ by $g\ge1$ moves around a simple alternating cycle $v=v^+-v^-$, that is $S_2=S_1+g\,v$. Their common counts are their entrywise minima. Suppose the common count at one distinguished cycle edge is $B$, the common counts at all other cycle edges are at least $\Lambda$, and $B\le2\Lambda$, $\Lambda\ge2g$. If a protocol on $[q]^N\times[q]^N$ using at most $c$ qubits with prior entanglement has type-averaged acceptance gap $|p(S_2)-p(S_1)|\ge1/(6q^3)$, then
--   $$c+1\ge b_q\,\frac{\sqrt{(B+g)\Lambda}}{g}. \tag{4.2}$$
--
--   This is the single-cycle lower bound that Theorem 4.1 reduces to.
--
--   Differences from the source:
--   - encoding: two types differ by g moves around a simple alternating cycle → S₂ = S₁ + g(v⁺ − v⁻) as integer tables for an AltCycle v; reason: the reversed orientation is again an alternating cycle signed matrix (start the cycle one row later)
--   - reading: arbitrary prior entanglement → an arbitrary input-independent unit start state on finitely many qubits W (W unbounded); reason: the standard finite-dimensional model of entanglement-assisted communication, the one of [LS09] and [SS24, Thm 2.22] on which the paper builds its quantum bounds (App. B.3); the paper never uses an infinite-dimensional state
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.4, p.16 (proof pp.16–17)

import Mathlib
import Definitions.Def_PermInvCC_AltCycle
import Definitions.Def_PermInvCC_EntQProtocol
import Definitions.Def_PermInvCC_typeAvgAccept

namespace PermInvCC

/-- **Lemma 4.4 (Quantum Lower Bound for an Alternating Cycle)** (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, p.16). Suppose two types differ by `g` moves
around a simple alternating cycle, where `g ≥ 1` is an integer. Their common counts are their
entrywise minima. Their common count at one distinguished edge is `B`, and their common counts at
all other cycle edges are at least `Λ`. Assume `B ≤ 2Λ` and `Λ ≥ 2g`. If a `c`-qubit protocol has
a type-averaged acceptance gap of at least `1/(6q³)` between the two types, then
`c + 1 ≥ b_q √((B + g)Λ) / g` (4.2) for a constant `b_q > 0`.

**Formalization Note.** "Differ by `g` moves around the cycle `v`" is `S₂ = S₁ + g(v⁺ − v⁻)` as
integer tables (the reversed orientation is the cycle read from another starting row). The two
types have total `N` (that of `S₂` follows) and the protocol acts on `[q]^N × [q]^N`. `b_q` is
chosen after `q` and before everything else; `Λ` is real. -/
theorem lemma_4_4 (q : ℕ) (hq : 2 ≤ q) :
    ∃ bq : ℝ, 0 < bq ∧
      ∀ (N : ℕ) (S₁ S₂ : Fin q → Fin q → ℕ), ∑ a, ∑ b, S₁ a b = N →
        ∀ (v : AltCycle q) (g : ℕ), 1 ≤ g →
          (∀ a b, (S₂ a b : ℤ) = S₁ a b + g * v.signed a b) →
          ∀ e₀ ∈ v.edges, ∀ (B : ℕ) (Λ : ℝ),
            min (S₁ e₀.1 e₀.2) (S₂ e₀.1 e₀.2) = B →
            (∀ e ∈ v.edges, e ≠ e₀ → Λ ≤ (min (S₁ e.1 e.2) (S₂ e.1 e.2) : ℕ)) →
            (B : ℝ) ≤ 2 * Λ → 2 * (g : ℝ) ≤ Λ →
            ∀ (c : ℕ) (P : EntQProtocol (Fin N → Fin q) (Fin N → Fin q)), P.cost ≤ c →
              1 / (6 * (q : ℝ) ^ 3) ≤ |typeAvgAccept P S₂ - typeAvgAccept P S₁| →
              bq * Real.sqrt (((B : ℝ) + g) * Λ) / g ≤ (c : ℝ) + 1 := by sorry

end PermInvCC
