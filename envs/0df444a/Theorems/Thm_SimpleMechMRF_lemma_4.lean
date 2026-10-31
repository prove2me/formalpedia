-- Prove2me | Theorems.Thm_SimpleMechMRF_lemma_4
-- name    : SimpleMechMRF.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:55.709277+00:00
-- url     : https://prove2.me/theorems/18637a10-bd0c-46ac-9175-f39718a673e3
-- title:
--   Lemma 4, p.11 — duality benchmark $\mathrm{Rev}(M,v,D)\le$ Single $+$ Non-Favorite $\le$ Single $+$ Tail $+$ Core
-- statement:
--   Let $D$ be a finite type distribution over the type space $T$, let the buyer's valuation be constrained additive with a downward-closed set system $\mathcal I$ of feasible bundles, and let $M=(\pi,p)$ be an IC and IR mechanism. Then
--
--   $$
--   \mathrm{Rev}(M,v,D)\;\le\;\textsc{Single}+\textsc{Non-Favorite}\;\le\;\textsc{Single}+\textsc{Tail}(r)+\textsc{Core}(r),
--   $$
--
--   with $\textsc{Single}=\sum_{t\in T}\sum_i f(t)\pi_i(t)\varphi_i(t_i\mid t_{-i})\mathbb 1[t\in R_i]$ built from the ironed conditional virtual values of Definition 7, and $\textsc{Non-Favorite}$, $\textsc{Tail}$, $\textsc{Core}$ as in the definitions module.
--
--   This is the Cai–Devanur–Weinberg duality benchmark adapted to dependent items by conditioning on $t_{-i}$; it holds for every finite distribution, not only for MRFs, and is the upper bound on the optimal revenue that the rest of the paper compares with simple mechanisms.
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: mechanism M = (π, p) with allocation probabilities π_i(t) → a sub-probability lottery σ over feasible bundles S ∈ I at each report, π_i(t) = Σ_{S∈I, i∈S} σ(t,S), utility E_{S∼σ(t')}[v(t,S)] − p(t'); reason: a randomized allocation of a constrained-additive buyer is a distribution over feasible bundles; for I = 2^[n] every π ∈ [0,1]^n arises; same mechanisms
--   - encoding: IC and IR (no misreport gains; nonnegative truthful utility) → IC and IR for true types and reports in the support T; reason: the standard finite-type model; types outside T have probability 0 and reports outside T are never needed
--   - reading: φ_i(t_i | t_{−i}) ironed over the interval [max_{j≠i} t_j, max Supp(D_{i|t−i})] → ironing (concave majorant of the conditional revenue curve) over the values s with (s, t_{−i}) ∈ T ∩ R_i; reason: R_i is the paper's region for the benchmark; the two sets differ only at s = max_{j≠i} t_j when a smaller index ties, which is not in R_i; checked numerically that Lemma 4 and the Def 7 property hold with this reading
--   - generalization: Lemma 4 with r = SRev(v, D) → every real r; reason: the proof splits the sum at r and never uses its value; specializes to r = SRev
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Lemma 4, p.11 (PDF 12); Definition 11, Appendix A, p.27 (PDF 28)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Lemma 4** (Benchmark of Optimal Revenue for Constrained Additive Valuations; Cai &
Oikonomou, *On Simple Mechanisms for Dependent Items*, arXiv:2106.10814v2, p. 11, PDF 12).
Let `D` be a finite type distribution, `I` a downward-closed set system of feasible bundles
(constrained additive valuation `v(t, S) = max_{R⊆S, R∈I} Σ_{i∈R} tᵢ`), and `M = (π, p)` an IC and
IR mechanism that randomizes over feasible bundles. Then
`Rev(M, v, D) ≤ Single + Non-Favorite ≤ Single + Tail(r) + Core(r)`,
where `Single` uses the ironed conditional virtual values `φᵢ(tᵢ | t₋ᵢ)` of Definition 7.

**Formalization Note.** The paper fixes `r = SRev(v, D)`; the statement here holds for every
real `r` and specializes to the paper's. -/
theorem lemma_4 {n : ℕ} (D : TypeDist n) (I : Finset (Finset (Fin n))) (hI : DownwardClosed I)
    (M : Mechanism n) (hM : M.IsLottery I) (hIC : M.IsIC D I) (hIR : M.IsIR D I) (r : ℝ) :
    M.rev D ≤ D.single I M + D.nonFavorite I M ∧
    D.single I M + D.nonFavorite I M ≤ D.single I M + D.tail r + D.core r := by sorry

end SimpleMechMRF
