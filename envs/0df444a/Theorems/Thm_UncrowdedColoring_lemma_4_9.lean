-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_9
-- name    : UncrowdedColoring.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:15:33.163866+00:00
-- url     : https://prove2.me/theorems/dcdd64a3-e67c-42cf-bd4b-3c43e49b411e
-- title:
--   Lemma 4.9 (corrected: $|L(v)|=\lceil q_i\rceil$) — discard probability
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   Let $(L,F)$ satisfy $P(i)$ with $i\in[s-1]$. For every $v\in U$ and $c\in L(v)$,
--   $$\mathbb P(c\in D(v))\le\sum_{\ell=2}^k\deg(F_c,\ell,v)\Big(\frac{\alpha}{q_i}\Big)^{\ell-1}\le 1-\mathrm{keep}_i.$$
--
--   In particular the bias (31) is at most $1$, so Step (3) of Algorithm 4.1 is well defined. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.9, p.25

import Mathlib
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_trialLaw

open scoped Classical

namespace UncrowdedColoring

/-- **Lemma 4.9**, p.25: both inequalities for the discard probability.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.9, p.25.

**Formalization Note.** `k ≥ 2`, `0 < ε < 1`, and `d ≥ d₀(k, ε)` are the standing assumptions of §4
(p.16); the input of Algorithm 4.1 satisfies `P(i)` for `i ∈ [s − 1]`. `P(c ∈ D(v))` is `discardProb`,
under the law of the activations and colors. The upper bound shows `P(c ∉ D(v)) ≥ keep_i`, so the clip
in `coin (eqBias …)` is inactive. -/
theorem lemma_4_9 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∀ v ∈ U, ∀ c ∈ L v,
          discardProb U L F ε d v c ≤
              ∑ ℓ ∈ Finset.Icc 2 k,
                (ellDegree (F c) ℓ v : ℝ) * (alpha ε d / qSeq k ε d i) ^ (ℓ - 1) ∧
            ∑ ℓ ∈ Finset.Icc 2 k,
                (ellDegree (F c) ℓ v : ℝ) * (alpha ε d / qSeq k ε d i) ^ (ℓ - 1) ≤
              1 - keep k ε d i := by sorry

end UncrowdedColoring
