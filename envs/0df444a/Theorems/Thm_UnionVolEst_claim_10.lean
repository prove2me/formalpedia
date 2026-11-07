-- Prove2me | Theorems.Thm_UnionVolEst_claim_10
-- name    : UnionVolEst.claim_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:27.349715+00:00
-- url     : https://prove2.me/theorems/7a5eeccc-b154-4b6d-a962-e270b9b6d068
-- title:
--   Claim 10 — a failure of Alpona-modified lies in $F_{\mathrm{vol}}\cup F_{\mathrm{prob}}\cup F_{\mathrm{good}}\cup F_{\mathrm{bad}}$ (corrected: adds $\mathrm{Fail}_{\mathrm{prob}}$)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   For every run of Alpona-modified whose output lies outside $[(1-\varepsilon)F_0,(1+\varepsilon)F_0]$, at least one of the following holds:
--   1. $\mathrm{Fail}_{\mathrm{vol}}$: some ComputeVolume answer is not a $\kappa$-factor approximation of its volume;
--   2. $\mathrm{Fail}_{\mathrm{prob}}$: $p_{\mathrm{final}}<1/F_0$;
--   3. $\mathrm{Fail}_{\mathrm{good}}$: all answers are correct, $p_{\mathrm{final}}\ge1/F_0$, and $\mathrm{Est}_{\mathrm{good}}\notin[(1-\tfrac{15}{32}\varepsilon)p_{\mathrm{final}}F_0',(1+\tfrac{15}{32}\varepsilon)p_{\mathrm{final}}F_0']$;
--   4. $\mathrm{Fail}_{\mathrm{bad}}$: all answers are correct, $p_{\mathrm{final}}\ge1/F_0$, and $\mathrm{Est}_{\mathrm{bad}}>\tfrac{15}{32}\varepsilon\,p_{\mathrm{final}}F_0'$.
--
--   **Formalization Note** Stated for every outcome of the randomness; $F_0'$ and the bad regions use the sampling distributions of the oracle model.
--
--   Differences from the source:
--   - correction: three events Fail_vol, Fail_good, Fail_bad → adds the fourth event Fail_prob = {p_final < 1/F₀}; reason: the proof concludes "the union of the above four events" and §5.1 counts four sources of failure; without Fail_prob the claim is false (M = 1, K₁ = [0,1]², exact oracles, any run with N₁ > threshold: one halving gives p_final = 1/2 and output 2N₁′ ∈ {0} ∪ [2, ∞), outside [1 − ε, 1 + ε], with correct volumes and p_final < 1/F₀)
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - generalization: M calls of ComputeVolume, each meeting its guarantee → a vector of volume answers with an arbitrary joint law, each marginal meeting the guarantee; reason: only the per-query guarantee is used; independent calls are a special case
--   - reading: "lies in (1 ± a)x" → closed interval |y − x| ≤ a·x; reason: the page writes both open-looking and closed intervals for the same events; the closed reading is the one Claim 9 and Lemma 16 item 3 use
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 10, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_goodVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_alponaOutput
import Definitions.Def_UnionVolEst_pFinal
import Definitions.Def_UnionVolEst_estGood
import Definitions.Def_UnionVolEst_estBad

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 10 (Decomposition of Failure) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.20, PDF p.22, corrected: if a run of
Alpona-modified returns a value outside `(1 ± ε)F₀`, then at least one of the following holds:
`Fail_vol` (some ComputeVolume answer is not a `κ`-factor approximation, `κ = ε/32`);
`Fail_prob` (`p_final < 1/F₀`); `Fail_good` (all answers correct, `p_final ≥ 1/F₀`, and
`Est_good ∉ (1 ± 15ε/32) p_final F′₀`); `Fail_bad` (all answers correct, `p_final ≥ 1/F₀`, and
`Est_bad > (15ε/32) p_final F′₀`).

**Formalization Note** (corrected: adds `Fail_prob`, the fourth event) The page lists only three
events, while its proof concludes "the union of the above four events" and §5.1 counts four
sources of failure. Without `Fail_prob` the claim is false (M = 1, `K₁ = [0,1]²`, exact oracles,
any run with `N₁ > threshold`: one halving gives `p_final = 1/2` and output `2N₁′ ∉ [1 − ε, 1 + ε]`).
Stated pointwise for every outcome `ω`; `F′₀` uses the model's sampling distributions. -/
theorem claim_10 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (ω : Ω)
    (hfail : alponaOutput (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) ∉
      Set.Icc ((1 - ε) * unionVolume K) ((1 + ε) * unionVolume K)) :
    (∃ i, ¬ IsVolumeApprox (ε / 32) (K i) (m.Vt i ω)) ∨
    pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) < 1 / unionVolume K ∨
    ((∀ i, IsVolumeApprox (ε / 32) (K i) (m.Vt i ω)) ∧
      1 / unionVolume K ≤ pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) ∧
      (estGood K m.D (ε / 32) ((alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω).elim [] AlponaState.X) : ℝ) ∉
        Set.Icc ((1 - 15 / 32 * ε) * pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) * goodVolume K m.D (ε / 32))
          ((1 + 15 / 32 * ε) * pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) * goodVolume K m.D (ε / 32))) ∨
    ((∀ i, IsVolumeApprox (ε / 32) (K i) (m.Vt i ω)) ∧
      1 / unionVolume K ≤ pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) ∧
      15 / 32 * ε * pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) * goodVolume K m.D (ε / 32) <
        (estBad K m.D (ε / 32) ((alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω).elim [] AlponaState.X) : ℝ)) := by sorry

end UnionVolEst
