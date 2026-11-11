-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_2_3
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:13.821223+00:00
-- url     : https://prove2.me/theorems/cba07d80-0fcc-41b7-9837-a0c484b62750
-- title:
--   Lemma 2.3 — YES/NO optimum gap
-- statement:
--   1. **YES.** For all $v,M,k$, every matrix $A$ and every outcome of the YES construction with any distinct marked indices $i\ne j$ (a $k$-subset $K$, a mask $Z$ of positive conditional probability, NO vectors $W$, and $V_j=1+W_i+Z$), the instance has $\mathrm{OPT}\le 3k$.
--
--   2. **NO, finite bound.** If $k\ge 8$, $\alpha\ge 1$ and $6\alpha e^{27\alpha}k\ln(2M+1)\le v$, then under the unconditioned NO distribution $P_0$ (matrix and vectors)
--   $$\Pr_{P_0}[\mathrm{OPT}\le 3\alpha k]\ \le\ \exp\!\big(-3\alpha k\ln(2M+1)\big).$$
--
--   3. **Asymptotics.** For the absolute constant $C_0$ of the regime (1) and all sequences satisfying it, $\Pr_{P_0}[\mathrm{OPT}\le3\alpha k]\to0$, and the NO probability conditioned on the good event,
--   $$\Pr_{P_0}[\mathrm{OPT}\le3\alpha k\mid A\in G]=\frac{\Pr_{P_0}[A\in G,\ \mathrm{OPT}\le 3\alpha k]}{\Pr[A\in G]},$$
--   also tends to $0$.
--
--   This is an averaged statement over matrices; it is not claimed for every fixed good matrix. Uncoverable NO outcomes have $\mathrm{OPT}=+\infty$ and do not count in the event.
--
--   Differences from the source:
--   - generalization: YES clause under the standing parameters of §2 (k ≥ 8, (1)) → YES clause for all v, M, k; reason: it follows from Lemma 2.1, valid for all parameters
--   - generalization: finite NO bound under all standing assumptions of §2 ((1) with k ≥ 8) → hypotheses k ≥ 8, α ≥ 1 and the lower bound 6αe^{27α}k ln(2M+1) ≤ v only; reason: the proof uses only these; the full regime implies them
--   - encoding: = o(1); conditioning on A ∈ G preserves the o(1) bound → Tendsto … atTop (𝓝 0) along every sequence satisfying (1) with an absolute C₀; the conditional probability as the ratio of the joint NO probability of {A good, OPT ≤ 3αk} to Pr[A good]; reason: literal meaning of o(1) and of conditioning on an event of A alone; C₀ is the constant for which Pr[G] ≥ 9/10
--   - generalization: parameters satisfying (1) (for every k) → (1) and α ≥ 1 required only for all sufficiently large k; reason: the conclusion is asymptotic in k; sequences satisfying (1) for every k satisfy it eventually
--   - encoding: OPT, the least weight of a cover → opt in WithTop ℝ, the minimum of the costs of all covers, ⊤ when no cover exists; reason: an exact minimum over a finite set; uncoverable inputs get +∞ instead of a junk value
--   - encoding: probability over the draw of A with independent Bernoulli(4/k) entries → probA: the finite sum of the product weights ∏(4/k or 1−4/k) over the matrices in the event; reason: the exact law of A on the finite set of matrices
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 2.3, printed p. 11 (PDF p. 12); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 2.3 (PDF p. 12): (i) every YES instance, for any distinct marked indices, has
`OPT ≤ 3k`; (ii) under the unconditioned NO distribution
`Pr_{P₀}[OPT ≤ 3αk] ≤ exp(-3αk ln(2M+1))` (standing assumptions `k ≥ 8`, `α ≥ 1` and the
lower bound on `v` from (1)); (iii) for the absolute `C₀` of (1), along every admissible parameter
family this probability is `o(1)`, and so is the NO probability conditioned on `A ∈ G`. -/
theorem lemma_2_3 :
    (∀ (v M k : ℕ) (A : Mat v M) (i j : Fin M), i ≠ j →
      ∀ K : Finset (Fin M), K.card = k → ∀ Z : Vec v, maskProb k A K Z ≠ 0 →
        ∀ W : Fin M → Vec v,
          (inst k A (Function.update W j (1 + W i + Z))).opt ≤ ((3 * (k : ℝ) : ℝ) : WithTop ℝ)) ∧
    (∀ (v M k : ℕ) (α : ℝ), 8 ≤ k → 1 ≤ α →
      6 * α * Real.exp (27 * α) * (k : ℝ) * Real.log (2 * (M : ℝ) + 1) ≤ (v : ℝ) →
        noJointProb k (fun (A : Mat v M) V =>
            (inst k A V).opt ≤ ((3 * α * (k : ℝ) : ℝ) : WithTop ℝ)) ≤
          Real.exp (-(3 * α * (k : ℝ) * Real.log (2 * (M : ℝ) + 1)))) ∧
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (α : ℕ → ℝ) (M v : ℕ → ℕ), ParamsEq1 C₀ α M v →
        Tendsto (fun k : ℕ => noJointProb k (fun (A : Mat (v k) (M k)) V =>
            (inst k A V).opt ≤ ((3 * α k * (k : ℝ) : ℝ) : WithTop ℝ))) atTop (𝓝 0) ∧
        Tendsto (fun k : ℕ =>
            noJointProb k (fun (A : Mat (v k) (M k)) V =>
              Good k A ∧ (inst k A V).opt ≤ ((3 * α k * (k : ℝ) : ℝ) : WithTop ℝ)) /
            probA k (fun A : Mat (v k) (M k) => Good k A)) atTop (𝓝 0) := by sorry

end StreamingWeightedSetCover1523.LowerBound
