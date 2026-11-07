-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_5_2
-- name    : UncrowdedColoring.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:18.636346+00:00
-- url     : https://prove2.me/theorems/bc32cb55-a49b-424d-8650-26444c73330b
-- title:
--   Lemma 5.2 (corrected: $|L(v)|=\lceil q_i\rceil$) — concentration (Conc1)–(Conc3)
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   Let $(L,F)$ satisfy $P(i)$ with $i\in[s-1]$, fix $v\in U$, $c\in L(v)$ and $2\le\ell\le j\le k$, and suppose $\deg(F_c,j,v)>0$. With $\tau_j$ as in (43), there is $C>0$ depending only on $k,\varepsilon$ such that
--
--   1. (Conc1) $\mathbb P\big(Y^{(1)}_{\ell,j}-\mathbb E[Y^{(1)}_{\ell,j}]\ge\tau_j/2\big)\le\exp(-Cd^{\frac{\eta/6}{k-1}})$;
--   2. (Conc2) $\mathbb P\big(Y^{(2)}_{\ell,j}\ge\tau_j/2\big)\le\exp(-Cd^{\frac{\eta/2}{k-1}})$;
--   3. (Conc3) $\mathbb P\big(Z^{(1)}_{\ell,j}-\mathbb E[Z^{(1)}_{\ell,j}]\le-\tau_j\big)\le\exp(-Cd^{\frac{\eta/6}{k-1}})$.
--
--   These are the tail bounds used in the proof of Lemma 4.13. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: P(·) = exp(−Ω(f(d))) → ∃ C > 0, ∃ d₀, ∀ d ≥ d₀, ∀ instance, P(·) ≤ exp(−C f(d)); reason: the convention of §3.1, p.14: implicit constants depend only on k, ε
--   - encoding: c_v chosen uniformly from L(v); P(eq(v, c) = 1) as in (31), a number in [0, 1] by Lemma 4.9 → c_v valued in ℕ with law supported on L(v); coin clips its parameter to [0, 1]; uniformColour is a Dirac mass on an empty list; reason: total laws; neither default is reached under P(i) for large d
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 5.2, p.32

import Mathlib
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_XVar

open scoped Classical
open MeasureTheory

namespace UncrowdedColoring

/-- **Lemma 5.2, (Conc1)–(Conc3)**, p.32.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 5.2, p.32, with `τ_j` from (43).

**Formalization Note.** `v`, `c`, `2 ≤ ℓ ≤ j ≤ k` are as fixed on pp.27, 30. `C` and `d₀` depend only
on `k`, `ε` and are quantified before the instance (§3.1, p.14). `P(i)` carries the correction
`|L(v)| = ⌈q_i⌉` (see `SatisfiesP`). -/
theorem lemma_5_2 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∀ v ∈ U, ∀ c ∈ L v, ∀ ℓ j : ℕ, 2 ≤ ℓ → ℓ ≤ j → j ≤ k →
          0 < ellDegree (F c) j v →
          -- (Conc1)
          (trialLaw k ε d i U L F).real
              {T | tauJ k ε d i ℓ j / 2 ≤
                Y1 F T ℓ j v c - ∫ T', Y1 F T' ℓ j v c ∂trialLaw k ε d i U L F} ≤
            Real.exp (-(C * d ^ ((eta ε / 6) / ((k : ℝ) - 1)))) ∧
          -- (Conc2)
          (trialLaw k ε d i U L F).real {T | tauJ k ε d i ℓ j / 2 ≤ Y2 F T ℓ j v c} ≤
            Real.exp (-(C * d ^ ((eta ε / 2) / ((k : ℝ) - 1)))) ∧
          -- (Conc3)
          (trialLaw k ε d i U L F).real
              {T | Z1 F T ℓ j v c - ∫ T', Z1 F T' ℓ j v c ∂trialLaw k ε d i U L F ≤
                -tauJ k ε d i ℓ j} ≤
            Real.exp (-(C * d ^ ((eta ε / 6) / ((k : ℝ) - 1)))) := by sorry

end UncrowdedColoring
