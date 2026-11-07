-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_8
-- name    : UncrowdedColoring.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:15:44.243392+00:00
-- url     : https://prove2.me/theorems/f034d0d0-e90e-43e7-8ffd-a0e361652b8a
-- title:
--   Lemma 4.8 (corrected: $|L(v)|=\lceil q_s\rceil$) — finishing blow
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   If $(L,F)$ satisfies $P(s)$, there is an $(L,F)$-compatible color assignment $\psi$ with $\mathrm{supp}(\psi)=U$.
--
--   This completes the coloring after the last nibble step. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.8, p.19

import Mathlib
import Definitions.Def_UncrowdedColoring_IsCompatible
import Definitions.Def_UncrowdedColoring_SatisfiesP

open scoped Classical

namespace UncrowdedColoring

/-- **Lemma 4.8 (Finishing blow)**, p.19.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.8, p.19.

**Formalization Note.** `k ≥ 2`, `0 < ε < 1`, and `d ≥ d₀(k, ε)` are the standing assumptions of §4
(p.16); `P(s)` carries the correction `|L(v)| = ⌈q_s⌉` (see `SatisfiesP`). `supp(L_s) = U`. -/
theorem lemma_4_8 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)),
        IsRestrictionFamily U L F → SatisfiesP k ε d (numSteps ε d) U L F →
        ∃ ψ : V → Option ℕ, IsPartialAssignment U ψ ∧ IsCompatible U L F ψ ∧
          ∀ v ∈ U, ψ v ≠ none := by sorry

end UncrowdedColoring
