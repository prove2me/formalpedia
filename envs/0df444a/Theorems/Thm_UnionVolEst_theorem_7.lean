-- Prove2me | Theorems.Thm_UnionVolEst_theorem_7
-- name    : UnionVolEst.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:19.438181+00:00
-- url     : https://prove2.me/theorems/685f899d-f494-42b6-a629-1b8a922377ec
-- title:
--   Theorem 7 — Alpona is an $(\varepsilon,\delta)$-approximate union volume estimator with $M$ volume and $\le M\cdot\mathrm{threshold}$ sampler calls (corrected: assumes $\mathrm{threshold}\le F_0$)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   Assume
--   $$
--   \mathrm{threshold}=\Big\lceil\frac{576}{\varepsilon^2}\log\frac{16M}{\delta}\Big\rceil\le F_0 .
--   $$
--   Then Alpona returns a value $\tilde V$ with
--   $$
--   \Pr\Big[\tilde V\notin\big[(1-\varepsilon)F_0,\ (1+\varepsilon)F_0\big]\Big]\le\delta,
--   $$
--   and every terminating run makes exactly $M$ calls to ComputeVolume and at most $M\cdot\mathrm{threshold}=O\big(M\varepsilon^{-2}\log(M/\delta)\big)$ calls to GenerateSamples.
--
--   This is the paper's main algorithmic result: a union-volume estimator that uses only PAC volume estimates and almost-uniform samples from the individual bodies, with sample complexity independent of the dimension except through the oracles.
--
--   **Formalization Note** A run that never terminates (a null event) outputs $0$, a failure.
--
--   Differences from the source:
--   - correction: no lower bound on the union volume → hypothesis threshold ≤ F₀; reason: without it the statement is false: M = 1, K₁ = [0, 1/10]² (a convex body, fat for r = 1/20, R = √2/20), exact oracles: the output |X|/p lies in {0} ∪ [1, ∞) because p starts at 1, so [(1 − ε)/100, (1 + ε)/100] is missed with probability 1 > δ
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - generalization: M calls of ComputeVolume, each meeting its guarantee → a vector of volume answers with an arbitrary joint law, each marginal meeting the guarantee; reason: only the per-query guarantee is used; independent calls are a special case
--   - reading: O(M) calls to the volume oracle and O(M ε⁻² log(M/δ)) calls to the sampler → exactly M volume calls and at most M · threshold sampler calls in every terminating run; reason: the explicit bounds the paper derives (p.28: at most threshold points inserted per iteration); threshold ≤ 576ε⁻² ln(16M/δ) + 1
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
--   - encoding: success with probability at least 1 − δ → failure event has probability at most δ; reason: equivalent for a measurable event and at least as strong otherwise
--   - encoding: Alpona's output on every run → output 0 on the null event where a halving loop never terminates; reason: the algorithm has no output there; 0 counts as a failure
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Theorem 7, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_alponaOutput

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Theorem 7 (Correctness and oracle efficiency of Alpona) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.17, PDF p.19, corrected:
for `M ≥ 1` bodies `K₁, …, K_M` and `ε, δ ∈ (0, 1)`, with oracles meeting the guarantees of §4.2
at the parameters of line 4 (`κ = ε/32`, `δ_v = δ/(4M)`, `η = ε/32`, `β = ε/(32M)`), if
`threshold = ⌈(576/ε²) log(16M/δ)⌉ ≤ F₀ = Vol(⋃ K_i)`, then Alpona returns a value outside
`[(1 − ε)F₀, (1 + ε)F₀]` with probability at most `δ`, and every terminating run makes exactly `M`
calls to ComputeVolume and at most `M · threshold` calls to GenerateSamples.

**Formalization Note** (corrected: adds `threshold ≤ F₀`) Without it the theorem is false: the
output `|X|/p` lies in `{0} ∪ [1, ∞)` because `p ≤ 1` starts at `1`, so for `M = 1`,
`K₁ = [0, 1/10]²` (a convex body) and exact oracles the interval `[(1 − ε)/100, (1 + ε)/100]` is
missed surely. The bodies are measurable sets of positive finite volume (convexity and
`(r, R)`-fatness serve only to implement the oracles). The failure event is bounded by `δ`
(equivalent to success with probability `≥ 1 − δ`). The printed `O(M)` and
`O(Mε⁻² log(M/δ))` call counts are made explicit as the sure bounds `M` and `M · threshold`
(`threshold ≤ 576ε⁻² ln(16M/δ) + 1`). A run that never terminates (a null event) outputs `0`. -/
theorem theorem_7 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (hT : (threshold ε δ M : ℝ) ≤ unionVolume K) :
    P {ω | alponaOutput (alponaRun none K ε δ m.Vt m.U m.Z m.C ω) ∉
        Set.Icc ((1 - ε) * unionVolume K) ((1 + ε) * unionVolume K)} ≤ ENNReal.ofReal δ ∧
      ∀ ω s, alponaRun none K ε δ m.Vt m.U m.Z m.C ω = some s →
        s.volCalls = M ∧ s.sampCalls ≤ M * threshold ε δ M := by sorry

end UnionVolEst
