-- Prove2me | Theorems.Thm_UnionVolEst_claim_8
-- name    : UnionVolEst.claim_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:13.098132+00:00
-- url     : https://prove2.me/theorems/ee502f7d-f6f5-4d35-9f16-5eb035f1575f
-- title:
--   Claim 8 — the TV distance between Alpona and Alpona-modified is at most $\Pr(\mathrm{Fail}_{\mathrm{prob}})$
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   Run Alpona and Alpona-modified (Algorithm 2, whose halving loop additionally requires $p\ge1/F_0$) with the same oracle answers and coins, and let $\mathrm{Fail}_{\mathrm{prob}}$ be the event that the final sampling intensity of Alpona-modified falls below $1/F_0$. Then the total variation distance between the output distributions is at most $\Pr(\mathrm{Fail}_{\mathrm{prob}})$: for every Borel set $A\subseteq\mathbb R$,
--   $$
--   \big|\Pr[\mathrm{Out}\in A]-\Pr[\mathrm{Out}_{\mathrm{mod}}\in A]\big| \le \Pr\big[p_{\mathrm{final}}^{\mathrm{mod}}<1/F_0\big].
--   $$
--   The claim lets the analysis work with Alpona-modified, whose intensity never drops far below $1/F_0$.
--
--   **Formalization Note** The total variation distance is the supremum over measurable sets, so the bound is stated for each measurable $A$; probabilities are compared as real numbers.
--
--   Differences from the source:
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - generalization: M calls of ComputeVolume, each meeting its guarantee → a vector of volume answers with an arbitrary joint law, each marginal meeting the guarantee; reason: only the per-query guarantee is used; independent calls are a special case
--   - encoding: total variation distance between the output distributions → |P(Out ∈ A) − P(Out_mod ∈ A)| for every measurable A ⊆ ℝ; reason: the total variation distance is the supremum of these quantities
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
--   - reading: log in the threshold → natural logarithm; reason: the proof of Claim 17 compares with ln(16M/δ)
--   - encoding: Alpona's output on every run → output 0 on the null event where a halving loop never terminates; reason: the algorithm has no output there
--   - encoding: Fail_prob: the intensity of Alpona falls below 1/F₀ → the final intensity of Alpona-modified is below 1/F₀; reason: the page makes this replacement right after the proof (p.19); under the shared randomness the two events coincide
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 8, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_alponaRun
import Definitions.Def_UnionVolEst_alponaOutput
import Definitions.Def_UnionVolEst_pFinal

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 8 (Closeness of Alpona and Alpona-modified) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.19, PDF p.21: the total
variation distance between the output distributions of Alpona and Alpona-modified is at most
`Pr(Fail_prob)`, where `Fail_prob` is the event that the sampling intensity of Alpona-modified at
the end of the run falls below `1/F₀` (printed p.19).

**Formalization Note** Both algorithms are driven by the same randomness of the oracle model
(the coupling of the proof is the identity coupling). The total variation distance is the
supremum over measurable sets `A` of `|P(O ∈ A) − P(O_mod ∈ A)|`; the bound is stated for every
measurable `A`, with probabilities read in `ℝ`. -/
theorem claim_8 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (A : Set ℝ) (hA : MeasurableSet A) :
    |(P {ω | alponaOutput (alponaRun none K ε δ m.Vt m.U m.Z m.C ω) ∈ A}).toReal -
        (P {ω | alponaOutput (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) ∈ A}).toReal| ≤
      (P {ω | pFinal (alponaRun (some (unionVolume K)) K ε δ m.Vt m.U m.Z m.C ω) < 1 / unionVolume K}).toReal := by sorry

end UnionVolEst
