-- Prove2me | Theorems.Thm_UnionVolEst_lemma_15
-- name    : UnionVolEst.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:13.26914+00:00
-- url     : https://prove2.me/theorems/c85eb9ef-5e34-45f8-b017-16a5e31a678f
-- title:
--   Lemma 15 — the counts $Y_j$ are independent with $Y_j\sim\mathrm{Pois}(q\tilde V_jD_j(\hat K_j\setminus\mathrm{Bad}_j))$ (corrected: fixed intensity)
-- statement:
--   Throughout, $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) are measurable sets of positive finite volume, $\varepsilon,\delta\in(0,1)$, and the oracles satisfy the guarantees of §4.2 with the parameters of line 4: ComputeVolume is a $(\kappa,\delta_v)$-PAC volume oracle with $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, and GenerateSamples returns independent points of $K_i$ with a law $D_i$ that is $(\eta,\beta)$-almost-$\ell_\infty$-close to the uniform distribution on $K_i$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$. $F_0=\mathrm{Vol}(\bigcup_i K_i)$, $\hat K_j$ are the unique sections, $\mathrm{Bad}_j$ the bad regions and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$.
--
--   The **fixed-intensity process** at intensity $q\in(0,1]$ runs Algorithm 1 with $p$ held at $q$ and no halving, with fixed volume answers $\tilde V_1,\dots,\tilde V_M$.
--
--   Let $\tilde V_j\ge0$ and $q\in(0,1]$, and let $Y_j$ be the number of points of the final multiset of the fixed-intensity process lying in $\hat K_j\setminus\mathrm{Bad}_j$. Then $Y_1,\dots,Y_M$ are mutually independent and, for each $j$,
--   $$
--   Y_j\sim\mathrm{Pois}\big(q\,\tilde V_j\,D_j(\hat K_j\setminus\mathrm{Bad}_j)\big).
--   $$
--
--   Differences from the source:
--   - correction: X ∼ Pois(p_final · …) with the random final intensity p_final → the law is stated for the fixed-intensity process at any fixed q ∈ (0, 1] (alponaFixed); reason: read as "given p_final = 2^(−t)" the printed law is false (M = 1, K₁ = [0,1]², exact oracles, Algorithm 2: on {p_final = 1} no halving occurred, so the count is at most threshold); the page's proof, Lemma 26 at one intensity, proves the fixed-intensity statement, which is how Claims 14, 17, 20 use it
--   - generalization: accurate volume answers Ṽ_j ∈ (1 ± ε/32) Vol(K_j) (after conditioning) → any fixed vector Ṽ_j ≥ 0; reason: the Poisson law does not use accuracy; accurate answers are nonnegative
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - encoding: oracle calls, Poisson draws and coin flips of Algorithm 1 → random variables of OracleModel on one probability space (samples lie in their body surely; Poisson draws by a uniform quantile; coins per body, round and position; volume answers independent of the rest); reason: a probability-space rendering of the algorithm and its oracles; same laws
--   - encoding: multiset X, intensity p, bodies 1..M → List, p = 2^(-level), bodies 0..M−1 (Fin M); reason: same objects
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Lemma 15, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_OracleModel
import Definitions.Def_UnionVolEst_uniqueSection
import Definitions.Def_UnionVolEst_badRegion
import Definitions.Def_UnionVolEst_countIn
import Definitions.Def_UnionVolEst_poissonQuantile
import Definitions.Def_UnionVolEst_alponaFixed

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Lemma 15 (Properties of `Y_j`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.24, PDF p.26, corrected (fixed intensity): in the fixed-intensity process
(Algorithm 1 with `p` held at `q ∈ (0, 1]`, no halving, fixed volume answers `Ṽ_j ≥ 0`), the
counts `Y_j = #{x ∈ X : x ∈ K̂_j \ Bad_j}` are mutually independent, and the `j`-th count has law
`Pois(q Ṽ_j D_j(·))` of the corresponding region.

**Formalization Note** (corrected: random `p_final` → fixed intensity `q`) The page writes the
law with the random final intensity `p_final`; read as "given `p_final = 2^{−t}`" (as Claims 14,
17, 20 use it) it is false: with `M = 1`, `K₁ = [0,1]²`, exact oracles and Algorithm 2, on
`{p_final = 1}` no halving occurred, so the count is at most `threshold`, not Poisson. The page's
proof (Lemma 26 at one intensity) proves the fixed-intensity statement given here. -/
theorem lemma_15 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : OracleModel P K (ε / 32) (δ / (4 * M)) (ε / 32) (ε / (32 * M)))
    (V : Fin M → ℝ) (hV : ∀ j, 0 ≤ V j) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    iIndepFun (fun j ω => countIn (alponaFixed q K V m.U m.Z ω) (uniqueSection K j \ badRegion K m.D (ε / 32) j)) P ∧
      ∀ j, HasLaw (fun ω => countIn (alponaFixed q K V m.U m.Z ω) (uniqueSection K j \ badRegion K m.D (ε / 32) j))
        (poissonMeasure (q * V j * (m.D j (uniqueSection K j \ badRegion K m.D (ε / 32) j)).toReal).toNNReal) P := by sorry

end UnionVolEst
