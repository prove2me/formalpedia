-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_7
-- name    : UncrowdedColoring.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:52.700723+00:00
-- url     : https://prove2.me/theorems/bf619d02-232c-405d-a626-2b388a409282
-- title:
--   Lemma 4.7 (corrected: $|L(v)|=\lceil q_i\rceil$) — one nibble step
-- statement:
--   Let $k\ge 2$, $0<\varepsilon<1$ and $d\ge d_0(k,\varepsilon)$. Let $F$ be a family of restriction hypergraphs with respect to a list assignment $L$ on a finite set $U$ such that $(L,F)$ satisfies $P(i)$ for some $i\in[s-1]$. There exist a partial color assignment $\psi$ for $U$, a list assignment $\tilde L$ on $\tilde U=U\setminus\mathrm{supp}(\psi)$ and a family $\tilde F$ of restriction hypergraphs with respect to $\tilde L$ such that
--
--   1. (R1) $\psi$ is $(L,F)$-compatible;
--   2. (R2) $(\tilde L,\tilde F)$ satisfies $P(i+1)$;
--   3. (R3) for every $(\tilde L,\tilde F)$-compatible partial color assignment $\tilde\psi$ for $\tilde U$, $\psi\cup\tilde\psi$ is $(L,F)$-compatible.
--
--   This is the step iterated $s-1$ times in the proof of Theorem 1.8. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.7, pp.18–19

import Mathlib
import Definitions.Def_UncrowdedColoring_IsCompatible
import Definitions.Def_UncrowdedColoring_SatisfiesP

open scoped Classical

namespace UncrowdedColoring

/-- **Lemma 4.7**, pp.18–19: one nibble step.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.7, pp.18–19.

**Formalization Note.** `k ≥ 2`, `0 < ε < 1`, and `d ≥ d₀(k, ε)` are the standing assumptions of §4
(p.16); `d₀` precedes the instance. `P(i)` carries the correction `|L(v)| = ⌈q_i⌉` (see `SatisfiesP`).
`L̃` and `F̃` are read only on `Ũ := U \ supp(ψ)`, the filter below. -/
theorem lemma_4_7 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∃ (ψ : V → Option ℕ) (Lt : V → Finset ℕ) (Ft : ℕ → Finset (Finset V)),
          IsPartialAssignment U ψ ∧
          IsRestrictionFamily (U.filter fun v => ψ v = none) Lt Ft ∧
          -- (R1)
          IsCompatible U L F ψ ∧
          -- (R2)
          SatisfiesP k ε d (i + 1) (U.filter fun v => ψ v = none) Lt Ft ∧
          -- (R3)
          ∀ ψt : V → Option ℕ, IsPartialAssignment (U.filter fun v => ψ v = none) ψt →
            IsCompatible (U.filter fun v => ψ v = none) Lt Ft ψt →
            IsCompatible U L F (unionAssign ψ ψt) := by sorry

end UncrowdedColoring
