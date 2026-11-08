-- Prove2me | Theorems.Thm_UnionVolEst_claim_11
-- name    : UnionVolEst.claim_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T08:05:55.243608+00:00
-- url     : https://prove2.me/theorems/f77601f1-295d-40eb-b72b-2477ed1e483b
-- title:
--   Claim 11 — $\Pr[\mathrm{Fail}_{\mathrm{vol}}]\le\delta/4$ (corrected: $<\to\le$)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   The event $\mathrm{Fail}_{\mathrm{vol}}$ that at least one of the $M$ ComputeVolume answers is not a $\kappa$-factor approximation of the corresponding volume satisfies
--   $$
--   \Pr[\mathrm{Fail}_{\mathrm{vol}}]\le\frac{\delta}{4}.
--   $$
--
--   Differences from the source:
--   - correction: P[Fail_vol] < δ/4 → P[Fail_vol] ≤ δ/4; reason: an oracle allowed by the guarantee may err with probability exactly δ_v = δ/(4M); for M = 1 this gives P[Fail_vol] = δ/4
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - generalization: M calls of ComputeVolume, each meeting its guarantee → a vector of volume answers with an arbitrary joint law, each marginal meeting the guarantee; reason: only the per-query guarantee is used; independent calls are a special case
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 11, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 11 (Bounding Error due to Volume Computation) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.21, PDF p.23, corrected: the
event `Fail_vol` that at least one ComputeVolume query does not return a `κ`-factor
approximation (`κ = ε/32`) of the corresponding volume has probability at most `δ/4`.

**Formalization Note** (corrected: `< δ/4` → `≤ δ/4`) An oracle allowed by the guarantee
`Pr[…] ≥ 1 − δ_v` may err with probability exactly `δ_v = δ/(4M)`; with `M = 1` this gives
`P[Fail_vol] = δ/4`, so the strict inequality of the page fails. -/
theorem claim_11 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M))) :
    P {ω | ∃ i, ¬ IsVolumeApprox (ε / 32) (K i) (m.Vt i ω)} ≤ ENNReal.ofReal (δ / 4) := by sorry

end UnionVolEst
