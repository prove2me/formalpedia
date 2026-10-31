-- Prove2me | Theorems.Thm_SimpleMechMRF_lemma_6
-- name    : SimpleMechMRF.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:04.613879+00:00
-- url     : https://prove2.me/theorems/4b14a0eb-ab40-44f8-a54c-f8a9450b1194
-- title:
--   Lemma 6, p.12 — Single $\le e^{4\Delta}\,\mathrm{SRev}$ and Tail $\le e^{4\Delta}\,\mathrm{SRev}$
-- statement:
--   Let the type distribution $D$ be a Markov random field with maximum weighted degree $\Delta$, and let $M$ be any IC and IR mechanism for an additive buyer. Then
--
--   $$
--   \textsc{Single}\;\le\;e^{4\Delta}\cdot\mathrm{SRev}\qquad\text{and}\qquad\textsc{Tail}\;\le\;e^{4\Delta}\cdot\mathrm{SRev},
--   $$
--
--   where $\textsc{Tail}$ is taken at the cutoff $r=\mathrm{SRev}=\sum_i r_i$. Together with Lemma 4 this leaves only the Core to be compared with simple mechanisms.
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: mechanism M = (π, p) with allocation probabilities π_i(t) → a sub-probability lottery σ over feasible bundles S ∈ I at each report, π_i(t) = Σ_{S∈I, i∈S} σ(t,S), utility E_{S∼σ(t')}[v(t,S)] − p(t'); reason: a randomized allocation of a constrained-additive buyer is a distribution over feasible bundles; for I = 2^[n] every π ∈ [0,1]^n arises; same mechanisms
--   - encoding: IC and IR (no misreport gains; nonnegative truthful utility) → IC and IR for true types and reports in the support T; reason: the standard finite-type model; types outside T have probability 0 and reports outside T are never needed
--   - reading: φ_i(t_i | t_{−i}) ironed over the interval [max_{j≠i} t_j, max Supp(D_{i|t−i})] → ironing (concave majorant of the conditional revenue curve) over the values s with (s, t_{−i}) ∈ T ∩ R_i; reason: R_i is the paper's region for the benchmark; the two sets differ only at s = max_{j≠i} t_j when a smaller index ties, which is not in R_i; checked numerically that Lemma 4 and the Def 7 property hold with this reading
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Lemma 6, p.12 (PDF 13); proof in Appendix C, pp.29–30 (PDF 30–31)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Lemma 6** (Cai & Oikonomou, *On Simple Mechanisms for Dependent Items*,
arXiv:2106.10814v2, p. 12, PDF 13). Let the type distribution `D` be the law of an MRF `G` with
maximum weighted degree `Δ`, and let `M` be any IC and IR mechanism for an additive buyer
(`I = 2^[n]`). Then `Single ≤ e^{4Δ} · SRev` and `Tail ≤ e^{4Δ} · SRev`, where `Tail` is taken at
the cutoff `r = SRev = Σᵢ rᵢ`.

**Formalization Note.** Alphabets are finite sets of nonnegative reals. `SRev` is
`Σᵢ sup_p p · Pr[tᵢ ≥ p]` (p. 12). -/
theorem lemma_6 {n : ℕ} (G : MRF n) (M : Mechanism n) (hM : M.IsLottery (additiveSystem n))
    (hIC : M.IsIC G.law (additiveSystem n)) (hIR : M.IsIR G.law (additiveSystem n)) :
    G.law.single (additiveSystem n) M ≤ Real.exp (4 * G.maxWeightedDegree) * srev G.law ∧
    G.law.tail (srev G.law) ≤ Real.exp (4 * G.maxWeightedDegree) * srev G.law := by sorry

end SimpleMechMRF
