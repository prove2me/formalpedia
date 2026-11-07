-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_13
-- name    : UncrowdedColoring.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:21.332052+00:00
-- url     : https://prove2.me/theorems/12fd7eb8-45b9-4bf4-8749-50515ec8e3e3
-- title:
--   Lemma 4.13 (corrected: $|L(v)|=\lceil q_i\rceil$) — the color-degree bad event
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   Let $(L,F)$ satisfy $P(i)$ with $i\in[s-1]$. Let $E_{v,c,\ell}$ be the event
--   $$X_\ell(v,c)>\binom{k-1}{\ell-1}\Big(\frac{\alpha\gamma_{i+1}}{q_{i+1}}\Big)^{k-\ell}\beta_{i+1}^{\ell-1}t_{i+1}.$$
--   There is $C>0$ depending only on $k,\varepsilon$ such that for every $v\in U$, $c\in L(v)$ and $2\le\ell\le k$,
--   $$\mathbb P(E_{v,c,\ell})\le\exp\big(-C\,d^{\frac{\eta/6}{k-1}}\big).$$
--
--   This controls the color degrees after one nibble step. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: P(·) = exp(−Ω(f(d))) → ∃ C > 0, ∃ d₀, ∀ d ≥ d₀, ∀ instance, P(·) ≤ exp(−C f(d)); reason: the convention of §3.1, p.14: implicit constants depend only on k, ε
--   - encoding: c_v chosen uniformly from L(v); P(eq(v, c) = 1) as in (31), a number in [0, 1] by Lemma 4.9 → c_v valued in ℕ with law supported on L(v); coin clips its parameter to [0, 1]; uniformColour is a Dirac mass on an empty list; reason: total laws; neither default is reached under P(i) for large d
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.13, p.28

import Mathlib
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_XVar

open scoped Classical

namespace UncrowdedColoring

/-- **Lemma 4.13**, p.28: `P(E_{v,c,ℓ}) = exp(−Ω(d^{(η/6)/(k−1)}))`, where `E_{v,c,ℓ}` is the event
`X_ℓ(v, c) > binom(k−1, ℓ−1) (αγ_{i+1}/q_{i+1})^{k−ℓ} β_{i+1}^{ℓ−1} t_{i+1}` (p.28).

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.13, p.28.

**Formalization Note.** `C` and `d₀` depend only on `k`, `ε` and are quantified before the instance
(§3.1, p.14); the bound is the upper-bound reading of `= exp(−Ω(·))`. `P(i)` carries the correction
`|L(v)| = ⌈q_i⌉` (see `SatisfiesP`). -/
theorem lemma_4_13 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∀ v ∈ U, ∀ c ∈ L v, ∀ ℓ : ℕ, 2 ≤ ℓ → ℓ ≤ k →
          (trialLaw k ε d i U L F).real
              {T | ((k - 1).choose (ℓ - 1) : ℝ) *
                    (alpha ε d * gammaSeq k ε d (i + 1) / qSeq k ε d (i + 1)) ^ (k - ℓ) *
                    betaSeq k ε d (i + 1) ^ (ℓ - 1) * tSeq k ε d (i + 1) <
                  XVar k F T ℓ v c} ≤
            Real.exp (-(C * d ^ ((eta ε / 6) / ((k : ℝ) - 1)))) := by sorry

end UncrowdedColoring
