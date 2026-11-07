-- Prove2me | Theorems.Thm_UnionVolEst_claim_14
-- name    : UnionVolEst.claim_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:12.366133+00:00
-- url     : https://prove2.me/theorems/a4af7f5b-0c59-43b6-b3a5-48cdb0b4ee8a
-- title:
--   Claim 14 — $\Pr[\mathrm{Fail}_{\mathrm{prob}}]<\delta/4$ (corrected: assumes $1\le F_0$)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   Run Alpona-modified with fixed accurate volume answers $(1-\varepsilon/32)\mathrm{Vol}(K_j)\le\tilde V_j\le(1+\varepsilon/32)\mathrm{Vol}(K_j)$, and assume $F_0\ge1$. Then the event $\mathrm{Fail}_{\mathrm{prob}}$ that $p_{\mathrm{final}}$ falls below $1/F_0$ satisfies $\Pr[\mathrm{Fail}_{\mathrm{prob}}]<\delta/4$.
--
--   Differences from the source:
--   - correction: no lower bound on the union volume → hypothesis 1 ≤ F₀; reason: exactly what is needed: if F₀ < 1 then 1/F₀ > 1 ≥ p_final surely and P[Fail_prob] = 1 (K₁ = [0, 1/10]², exact oracles, F₀ = 1/100); the goal's threshold ≤ F₀ implies it
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - encoding: volume answers fixed to an accurate outcome by conditioning (p.21) → a deterministic vector Ṽ with (1 − ε/32)Vol(K_j) ≤ Ṽ_j ≤ (1 + ε/32)Vol(K_j); reason: the page states that it fixes such an outcome from here on; volume answers are independent of the remaining randomness
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 14, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_pFinal

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 14 (Bounding Probability of `Fail_prob`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.22, PDF p.24, corrected: for
Alpona-modified run with fixed accurate volume answers `Ṽ_j ∈ (1 ± ε/32) Vol(K_j)`, if
`1 ≤ F₀`, the event `Fail_prob` that `p_final` falls below `1/F₀` has probability less
than `δ/4`.

**Formalization Note** (corrected: adds `1 ≤ F₀`) Without it the claim fails: if `F₀ < 1` then
`1/F₀ > 1 ≥ p_final` surely and `P[Fail_prob] = 1` (e.g. `K₁ = [0, 1/10]²`, `F₀ = 1/100`). The
hypothesis is exactly the necessary one; the goal's `threshold ≤ F₀` implies it. The volume answers are fixed, as on the page ("we fix an outcome of all the
volume queries in which every query returns an accurate estimate", printed p.21). -/
theorem claim_14 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (V : Fin M → ℝ) (hV : ∀ j, IsVolumeApprox (ε / 32) (K j) (V j)) (hF : 1 ≤ unionVolume K) :
    P {ω | pFinal (alponaRun (some (unionVolume K)) K ε δ (fun i _ => V i) m.U m.Z m.C ω) < 1 / unionVolume K} < ENNReal.ofReal (δ / 4) := by sorry

end UnionVolEst
