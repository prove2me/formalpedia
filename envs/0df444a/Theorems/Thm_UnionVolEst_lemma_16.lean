-- Prove2me | Theorems.Thm_UnionVolEst_lemma_16
-- name    : UnionVolEst.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:39.317978+00:00
-- url     : https://prove2.me/theorems/e29518b0-8991-4b20-b892-90b1161b2968
-- title:
--   Lemma 16 — $\mathrm{Est}_{\mathrm{good}}\sim\mathrm{Pois}(q\Lambda_Y)$ and the bounds on $\Lambda_Y$ (corrected: fixed intensity)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   The **fixed-intensity process** at intensity $q\in(0,1]$ runs Algorithm 1 with $p$ held at $q$ and no halving, with fixed volume answers $\tilde V_1,\dots,\tilde V_M$.
--
--   Let the volume answers be accurate, $(1-\varepsilon/32)\mathrm{Vol}(K_j)\le\tilde V_j\le(1+\varepsilon/32)\mathrm{Vol}(K_j)$, let $q\in(0,1]$, $\Lambda:=\sum_j\tilde V_jD_j(\hat K_j)$ and $\Lambda_Y:=\sum_j\tilde V_jD_j(\hat K_j\setminus\mathrm{Bad}_j)$. Then $\mathrm{Est}_{\mathrm{good}}$ of the final multiset of the fixed-intensity process satisfies $\mathrm{Est}_{\mathrm{good}}\sim\mathrm{Pois}(q\Lambda_Y)$, and
--   1. $\big(1-\frac{\varepsilon}{15}\big)F_0'\le\Lambda_Y\le\big(1+\frac{\varepsilon}{15}\big)F_0'$;
--   2. $\Lambda_Y\ge\Lambda/2$;
--   3. $\big[(1-\frac{\varepsilon}{8})\Lambda_Y,(1+\frac{\varepsilon}{8})\Lambda_Y\big]\subseteq\big[(1-\frac{15}{32}\varepsilon)F_0',(1+\frac{15}{32}\varepsilon)F_0'\big]$.
--
--   Differences from the source:
--   - correction: X ∼ Pois(p_final · …) with the random final intensity p_final → the law is stated for the fixed-intensity process at any fixed q ∈ (0, 1] (alponaFixed); reason: read as "given p_final = 2^(−t)" the printed law is false (M = 1, K₁ = [0,1]², exact oracles, Algorithm 2: on {p_final = 1} no halving occurred, so the count is at most threshold); the page's proof, Lemma 26 at one intensity, proves the fixed-intensity statement, which is how Claims 14, 17, 20 use it
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - encoding: volume answers fixed to an accurate outcome by conditioning (p.21) → a deterministic vector Ṽ with (1 − ε/32)Vol(K_j) ≤ Ṽ_j ≤ (1 + ε/32)Vol(K_j); reason: the page states that it fixes such an outcome from here on; volume answers are independent of the remaining randomness
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Lemma 16, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_uniqueSection
import Definitions.Def_UnionVolEst_badRegion
import Definitions.Def_UnionVolEst_goodVolume
import Definitions.Def_UnionVolEst_countIn
import Definitions.Def_UnionVolEst_estGood
import Definitions.Def_UnionVolEst_poissonQuantile
import Definitions.Def_UnionVolEst_alponaFixed

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Lemma 16 (Properties of `Est_good`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.24, PDF p.26, Poisson clause corrected: with
`Λ_Y := Σ_j Ṽ_j D_j(K̂_j \ Bad_j)`, `Λ := Σ_j Ṽ_j D_j(K̂_j)` and accurate answers
`Ṽ_j ∈ (1 ± ε/32) Vol(K_j)`: in the fixed-intensity process at `q ∈ (0, 1]`,
`Est_good ∼ Pois(qΛ_Y)`; and (1) `(1 − ε/15) F′₀ ≤ Λ_Y ≤ (1 + ε/15) F′₀`, (2) `Λ_Y ≥ Λ/2`,
(3) `[(1 − ε/8)Λ_Y, (1 + ε/8)Λ_Y] ⊆ [(1 − 15ε/32) F′₀, (1 + 15ε/32) F′₀]`.

**Formalization Note** (corrected: random `p_final` → fixed intensity `q`) As for Lemma 12;
items 1–3 as printed. -/
theorem lemma_16 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (V : Fin M → ℝ) (hV : ∀ j, IsVolumeApprox (ε / 32) (K j) (V j)) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasLaw (fun ω => estGood K m.D (ε / 32) (alponaFixed q K V m.U m.Z ω))
        (poissonMeasure (q * (∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal)).toNNReal) P ∧
      ((1 - ε / 15) * goodVolume K m.D (ε / 32) ≤ ∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal ∧
        ∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal ≤ (1 + ε / 15) * goodVolume K m.D (ε / 32)) ∧
      (∑ j, V j * (m.D j (uniqueSection K j)).toReal) / 2 ≤ ∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal ∧
      Set.Icc ((1 - ε / 8) * (∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal)) ((1 + ε / 8) * (∑ j, V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal)) ⊆
        Set.Icc ((1 - 15 / 32 * ε) * goodVolume K m.D (ε / 32)) ((1 + 15 / 32 * ε) * goodVolume K m.D (ε / 32)) := by sorry

end UnionVolEst
