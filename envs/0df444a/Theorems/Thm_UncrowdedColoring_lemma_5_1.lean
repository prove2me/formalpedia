-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_5_1
-- name    : UncrowdedColoring.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:43.967515+00:00
-- url     : https://prove2.me/theorems/ae5c3e8a-e6cd-4746-8b8f-ddabf8099629
-- title:
--   Lemma 5.1 (corrected: $|L(v)|=\lceil q_i\rceil$) — expectations (Exp1)–(Exp3)
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   Let $(L,F)$ satisfy $P(i)$ with $i\in[s-1]$, and fix $v\in U$, $c\in L(v)$ and $2\le\ell\le j\le k$. Write $B=\binom{k-1}{\ell-1}\binom{k-\ell}{j-\ell}$. Then
--
--   1. (Exp1) $\mathbb E[Z^{(1)}_{\ell,j}]\le\mathbb E[Y^{(1)}_{\ell,j}]\le B(\alpha/q_i)^{k-\ell}\mathrm{uncolor}_i^{\ell-1}\beta_i^{j-1}\gamma_i^{k-j}t_i$;
--   2. (Exp2) $\mathbb E[Y^{(2)}_{\ell,j}]\le B(\alpha/q_i)^{k-1}\gamma_i^{k-j}\beta_i^{j-1}t_i$;
--   3. (Exp3) $\mathbb E[Y^{(1)}_{\ell,j}-Z^{(1)}_{\ell,j}]\le B(\alpha/q_i)^{k-\ell}\mathrm{uncolor}_i^{\ell-1}[(1+5/q_i)\beta_i\mathrm{keep}_i]^{j-1}\gamma_i^{k-j}t_i$.
--
--   These are the means used in the proof of Lemma 4.13. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: c_v chosen uniformly from L(v); P(eq(v, c) = 1) as in (31), a number in [0, 1] by Lemma 4.9 → c_v valued in ℕ with law supported on L(v); coin clips its parameter to [0, 1]; uniformColour is a Dirac mass on an empty list; reason: total laws; neither default is reached under P(i) for large d
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 5.1, p.32

import Mathlib
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_XVar

open scoped Classical
open MeasureTheory

namespace UncrowdedColoring

/-- **Lemma 5.1, (Exp1)–(Exp3)**, p.32.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 5.1, p.32.

**Formalization Note.** `v`, `c`, `2 ≤ ℓ ≤ j ≤ k` are as fixed on pp.27, 30. The variables `Y1`, `Y2`,
`Z1` are bounded functions on a discrete space, so the integrals are true expectations
(`Solutions/verification/UncrowdedColoring_sanity.lean` proves their integrability). `P(i)` carries the
correction `|L(v)| = ⌈q_i⌉` (see `SatisfiesP`). -/
theorem lemma_5_1 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∀ v ∈ U, ∀ c ∈ L v, ∀ ℓ j : ℕ, 2 ≤ ℓ → ℓ ≤ j → j ≤ k →
          -- (Exp1)
          (∫ T, Z1 F T ℓ j v c ∂trialLaw k ε d i U L F ≤
              ∫ T, Y1 F T ℓ j v c ∂trialLaw k ε d i U L F ∧
            ∫ T, Y1 F T ℓ j v c ∂trialLaw k ε d i U L F ≤
              ((k - 1).choose (ℓ - 1) : ℝ) * ((k - ℓ).choose (j - ℓ) : ℝ) *
                (alpha ε d / qSeq k ε d i) ^ (k - ℓ) * uncolor k ε d i ^ (ℓ - 1) *
                betaSeq k ε d i ^ (j - 1) * gammaSeq k ε d i ^ (k - j) * tSeq k ε d i) ∧
          -- (Exp2)
          (∫ T, Y2 F T ℓ j v c ∂trialLaw k ε d i U L F ≤
              ((k - 1).choose (ℓ - 1) : ℝ) * ((k - ℓ).choose (j - ℓ) : ℝ) *
                (alpha ε d / qSeq k ε d i) ^ (k - 1) * gammaSeq k ε d i ^ (k - j) *
                betaSeq k ε d i ^ (j - 1) * tSeq k ε d i) ∧
          -- (Exp3)
          ∫ T, (Y1 F T ℓ j v c - Z1 F T ℓ j v c) ∂trialLaw k ε d i U L F ≤
            ((k - 1).choose (ℓ - 1) : ℝ) * ((k - ℓ).choose (j - ℓ) : ℝ) *
              (alpha ε d / qSeq k ε d i) ^ (k - ℓ) * uncolor k ε d i ^ (ℓ - 1) *
              ((1 + 5 / qSeq k ε d i) * betaSeq k ε d i * keep k ε d i) ^ (j - 1) *
              gammaSeq k ε d i ^ (k - j) * tSeq k ε d i := by sorry

end UncrowdedColoring
