-- Prove2me | Theorems.Thm_UnionVolEst_claim_17
-- name    : UnionVolEst.claim_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:13.61947+00:00
-- url     : https://prove2.me/theorems/58916eee-c87f-42a5-98ce-fa73dcaa0c94
-- title:
--   Claim 17 — $\Pr[\mathrm{Fail}_{\mathrm{good}}]<\delta/4$ (corrected: assumes $\mathrm{threshold}\le F_0$)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   Run Alpona-modified with fixed accurate volume answers and assume $\mathrm{threshold}\le F_0$. Then the event $\mathrm{Fail}_{\mathrm{good}}$ that
--   $$
--   \mathrm{Est}_{\mathrm{good}}\notin\Big[\Big(1-\frac{15}{32}\varepsilon\Big)p_{\mathrm{final}}F_0',\ \Big(1+\frac{15}{32}\varepsilon\Big)p_{\mathrm{final}}F_0'\Big]
--   $$
--   has probability less than $\delta/4$.
--
--   Differences from the source:
--   - correction: no lower bound on the union volume → hypothesis threshold ≤ F₀; reason: without it the statement is false: M = 1, K₁ = [0,1]², exact oracles, ε = δ = 1/2: threshold = 7986, Bad = ∅, F′₀ = 1 and Fail_good ⊇ {N₁ = 0}, so P[Fail_good] ≥ e^(−1) > δ/4
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - encoding: volume answers fixed to an accurate outcome by conditioning (p.21) → a deterministic vector Ṽ with (1 − ε/32)Vol(K_j) ≤ Ṽ_j ≤ (1 + ε/32)Vol(K_j); reason: the page states that it fixes such an outcome from here on; volume answers are independent of the remaining randomness
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 17, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_goodVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_pFinal
import Definitions.Def_UnionVolEst_estGood

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 17 (Bounding Probability of `Fail_good`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.25, PDF p.27, corrected: for
Alpona-modified with fixed accurate volume answers `Ṽ_j ∈ (1 ± ε/32) Vol(K_j)`, if
`threshold ≤ F₀`, the event `Fail_good` (`Est_good ∉ [(1 − 15ε/32) p_final F′₀, (1 + 15ε/32) p_final F′₀]`) has
probability less than `δ/4`.

**Formalization Note** (corrected: adds `threshold ≤ F₀`) Without it the claim fails:
`M = 1`, `K₁ = [0,1]²`, exact oracles, `ε = δ = 1/2`: `threshold = 7986`, `Bad = ∅`, `F′₀ = 1`, and
`Fail_good ⊇ {N₁ = 0}`, so `P[Fail_good] ≥ e^{−1} > δ/4`. The event is the one displayed in
Claim 17, without the clause "`p_final ≥ 1/F₀`" of Claim 10's event, which it therefore contains;
"all ComputeVolume answers correct" holds by the fixed accurate answers. -/
theorem claim_17 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (V : Fin M → ℝ) (hV : ∀ j, IsVolumeApprox (ε / 32) (K j) (V j)) (hT : (threshold ε δ M : ℝ) ≤ unionVolume K) :
    P {ω | (estGood K m.D (ε / 32) ((alponaRun (some (unionVolume K)) K ε δ (fun i _ => V i) m.U m.Z m.C ω).elim [] AlponaState.X) : ℝ) ∉
          Set.Icc ((1 - 15 / 32 * ε) * pFinal (alponaRun (some (unionVolume K)) K ε δ (fun i _ => V i) m.U m.Z m.C ω) * goodVolume K m.D (ε / 32))
            ((1 + 15 / 32 * ε) * pFinal (alponaRun (some (unionVolume K)) K ε δ (fun i _ => V i) m.U m.Z m.C ω) * goodVolume K m.D (ε / 32))} <
      ENNReal.ofReal (δ / 4) := by sorry

end UnionVolEst
