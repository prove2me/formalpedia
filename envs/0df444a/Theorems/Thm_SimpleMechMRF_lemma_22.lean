-- Prove2me | Theorems.Thm_SimpleMechMRF_lemma_22
-- name    : SimpleMechMRF.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:02.568597+00:00
-- url     : https://prove2.me/theorems/450c6129-5029-47ea-89a5-ed0377d67527
-- title:
--   Lemma 22, p.27 — Non-Favorite $\le$ Tail $+$ Core
-- statement:
--   Let $D$ be a finite type distribution, $\mathcal I$ a set system of feasible bundles, and $M$ a mechanism randomizing over feasible bundles, with allocation probabilities $\pi_i(t)\in[0,1]$. For every cutoff $r\in\mathbb R$,
--
--   $$
--   \textsc{Non-Favorite}=\sum_{t\in T}\sum_{i}f(t)\,\pi_i(t)\,t_i\,\mathbb 1[t\notin R_i]\;\le\;\underbrace{\sum_i\sum_{t_i>r}f_i(t_i)\,t_i\Pr_{t'\sim D}[t'\notin R_i\mid t_i'=t_i]}_{\textsc{Tail}}+\underbrace{\sum_i\sum_{t_i\le r}f_i(t_i)\,t_i}_{\textsc{Core}} .
--   $$
--
--   This is the second inequality of the benchmark of Lemma 4: the revenue a mechanism could collect from items that are not the buyer's favourite splits into the high values ($>r$) and the truncated values ($\le r$).
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: mechanism M = (π, p) with allocation probabilities π_i(t) → a sub-probability lottery σ over feasible bundles S ∈ I at each report, π_i(t) = Σ_{S∈I, i∈S} σ(t,S), utility E_{S∼σ(t')}[v(t,S)] − p(t'); reason: a randomized allocation of a constrained-additive buyer is a distribution over feasible bundles; for I = 2^[n] every π ∈ [0,1]^n arises; same mechanisms
--   - generalization: Lemma 22 with r = SRev(v, D) → every real r; reason: the proof splits the sum at r and never uses its value; specializes to r = SRev
--   - generalization: M the IC and IR mechanism of Lemma 4 for a constrained additive valuation (downward-closed I) → any mechanism that is a lottery over the bundles of any set system I (no IC, IR or downward closure); reason: the proof uses only 0 ≤ π_i(t) ≤ 1; specializes to the paper's mechanisms
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Lemma 22, Appendix A, p.27 (PDF 28)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Lemma 22** (Cai & Oikonomou, *On Simple Mechanisms for Dependent Items*,
arXiv:2106.10814v2, Appendix A, p. 27, PDF 28). For any finite type distribution `D`, any
set system `I`, any mechanism `M` whose allocation at each report is a lottery over the bundles
of `I` (so `0 ≤ πᵢ(t) ≤ 1`), and any cutoff `r ∈ ℝ`:
`Non-Favorite ≤ Tail(r) + Core(r)`, where
`Tail(r) = Σᵢ Σ_{tᵢ>r} fᵢ(tᵢ) · tᵢ · Pr_{t'∼D}[t' ∉ Rᵢ | t'ᵢ = tᵢ]` and
`Core(r) = Σᵢ Σ_{tᵢ≤r} fᵢ(tᵢ) · tᵢ`.

**Formalization Note.** In the paper `r = SRev(v, D)` and `M` is the IC and IR mechanism of
Lemma 4; the statement here holds for every real `r` and every lottery mechanism, and
specializes to the paper's. -/
theorem lemma_22 {n : ℕ} (D : TypeDist n) (I : Finset (Finset (Fin n))) (M : Mechanism n)
    (hM : M.IsLottery I) (r : ℝ) :
    D.nonFavorite I M ≤ D.tail r + D.core r := by sorry

end SimpleMechMRF
