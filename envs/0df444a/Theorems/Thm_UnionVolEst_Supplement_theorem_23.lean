-- Prove2me | Theorems.Thm_UnionVolEst_Supplement_theorem_23
-- name    : UnionVolEst.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:11:32.286127+00:00
-- url     : https://prove2.me/theorems/5521c319-cffb-4e40-b07a-aa159f2fccd3
-- title:
--   Theorem 23 — Alpona with $\beta=\varepsilon/(32\tau)$ on frequency-$\tau$ streams is $(\varepsilon,\delta)$-correct (corrected: assumes $\mathrm{threshold}\le F_0$)
-- statement:
--   This is the correctness of Alpona for bounded frequency streams.
--
--   Let $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) be measurable sets of positive finite volume with frequency at most $\tau\ge1$: every point lies in at most $\tau$ of them. Let $\varepsilon,\delta\in(0,1)$. Run Alpona (Algorithm 1) with oracles meeting the guarantees of §4.2, with the sampler parameter changed to $\beta=\varepsilon/(32\tau)$ and every other parameter unchanged:
--
--   1. ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$ and $\delta_v=\delta/(4M)$;
--   2. GenerateSamples returns independent points of $K_i$ from a distribution $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, with $\eta=\varepsilon/32$ and $\beta=\varepsilon/(32\tau)$;
--   3. the storage threshold is $\mathrm{threshold}=\lceil(576/\varepsilon^2)\log(16M/\delta)\rceil$.
--
--   If $\mathrm{threshold}\le F_0=\mathrm{Vol}\big(\bigcup_iK_i\big)$, then
--   $$
--   \Pr\Big[\widetilde V\notin\big[(1-\varepsilon)F_0,\,(1+\varepsilon)F_0\big]\Big]\;\le\;\delta,
--   $$
--   where $\widetilde V$ is the output of Alpona.
--
--   For streams of small frequency, the theorem lets the samplers run at accuracy $\varepsilon/(32\tau)$ instead of $\varepsilon/(32M)$, which shortens the Hit-and-Run walks.
--
--   **Formalization Note** The oracles and the run are the published `OracleModel` and `alponaRun` of Theorem 7. A run that never terminates, a null event, outputs $0$.
--
--   Differences from the source:
--   - correction: no lower bound on the union volume → hypothesis threshold = ⌈(576/ε²) log(16M/δ)⌉ ≤ F₀; reason: without it the statement is false: M = τ = 1 (frequency at most 1), K₁ = [0, 1/10]², exact oracles; the output |X|/p lies in {0} ∪ [1, ∞) because p starts at 1, so [(1 − ε)/100, (1 + ε)/100] is missed with probability 1 > δ; this is the correction of the published Theorem 7 (UnionVolEst.theorem_7)
--   - generalization: a collection of convex bodies with frequency at most τ → measurable sets of positive finite volume with frequency at most τ; reason: convexity serves only to implement the oracles, as in the base mission's Theorem 7; every convex body of positive volume is such a set
--   - generalization: 1 ≤ τ ≤ M ('by definition, we shall always have', p.34) → 1 ≤ τ; τ ≤ M not assumed; reason: for τ > M the oracle guarantee with β = ε/(32τ) is stronger than at τ = M; the statement specializes to the source
--   - generalization: M calls of ComputeVolume, each meeting its guarantee → a vector of volume answers with an arbitrary joint law, each marginal meeting the guarantee; reason: only the per-query guarantee is used; independent calls are a special case (as in the published Theorem 7)
--   - reading: run Alpona with β ← ε/(32τ) and keep all the other parameters unchanged → OracleModel at (κ, δ_v, η, β) = (ε/32, δ/(4M), ε/32, ε/(32τ)) and alponaRun none with threshold ⌈(576/ε²) log(16M/δ)⌉; reason: β is a parameter of the sampler only (line 4); the threshold and the other oracle parameters keep their line-4 values
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
--   - encoding: with probability at least 1 − δ the output lies in (1 ± ε)F₀ → the event that the output lies outside [(1 − ε)F₀, (1 + ε)F₀] has probability at most δ; reason: equivalent for a measurable event, at least as strong otherwise; closed interval
--   - encoding: Alpona's output, oracle calls, Poisson draws and coin flips → the published OracleModel random variables on one probability space; output 0 on the null event where a halving loop never terminates; reason: the base mission's rendering of Algorithm 1 and its oracles; 0 counts as a failure
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Theorem 23, §7, p.35 (PDF p.37); Definition 3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_alponaOutput
import Definitions.Def_UnionVolEst_Supplement_HasFrequencyAtMost

open MeasureTheory ProbabilityTheory

namespace UnionVolEst.Supplement

/-- Theorem 23 (Correctness of Alpona for Bounded Frequency Streams)
(Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*,
arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §7, printed p.35, PDF p.37), corrected:
for `M ≥ 1` bodies `K₁, …, K_M` of frequency at most `τ ≥ 1` (Definition 3) and `ε, δ ∈ (0, 1)`,
run Alpona (Algorithm 1) with oracles meeting the §4.2 guarantees at the line-4 parameters except
`β ← ε/(32τ)` (`κ = ε/32`, `δ_v = δ/(4M)`, `η = ε/32`). If
`threshold = ⌈(576/ε²) log(16M/δ)⌉ ≤ F₀ = Vol(⋃ K_i)`, the output lies outside
`[(1 − ε)F₀, (1 + ε)F₀]` with probability at most `δ`.

**Formalization Note** (corrected: adds `threshold ≤ F₀`, the correction of the published
`UnionVolEst.theorem_7`) Without it the theorem is false: for `M = τ = 1`, `K₁ = [0, 1/10]²` and
exact oracles the output lies in `{0} ∪ [1, ∞)`, which misses `[(1 − ε)/100, (1 + ε)/100]`
surely. Only the sampler parameter `β` changes; the algorithm `alponaRun none` and its threshold
are those of Algorithm 1 (`τ` enters only through the oracle guarantee, "τ is known to the
algorithm beforehand"). The bodies are measurable sets of positive finite volume, as in the base
mission. The page's remark `τ ≤ M` is dropped. Success with probability `≥ 1 − δ` is stated as
failure with probability `≤ δ`. A run that never terminates (a null event) outputs `0`. -/
theorem theorem_23 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (τ : ℕ) (hτ : 1 ≤ τ) (hfreq : HasFrequencyAtMost K τ)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * τ)))
    (hT : (threshold ε δ M : ℝ) ≤ unionVolume K) :
    P {ω | alponaOutput (alponaRun none K ε δ m.Vt m.U m.Z m.C ω) ∉
        Set.Icc ((1 - ε) * unionVolume K) ((1 + ε) * unionVolume K)} ≤ ENNReal.ofReal δ := by sorry

end UnionVolEst.Supplement
