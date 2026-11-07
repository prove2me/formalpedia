-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_3_1
-- name    : SmoothedMIS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:59.778311+00:00
-- url     : https://prove2.me/theorems/be07ca8c-7872-46e2-b842-af6fec2180fb
-- title:
--   Lemma 3.1 — smoothed diameter of a large two-hop neighbourhood is at most $200\sqrt{\ln n}$
-- statement:
--   Let $c'\ge1$ be a constant for which the bound of Lemma 2.2 holds, and $\beta\ge1$. There is $n_0$, depending only on $c'$ and $\beta$, such that for all $n\ge n_0$ the following holds. Let $G$ be a base graph on $n$ vertices, $F$ a subgraph of $G$, $s$ an integer with $e^{0.49\sqrt{\ln n}}\le s\le B_0$, and $Q$ a set of seeds with $\deg_F(v)>s$ for $v\in Q$. If $Z=N^2_F[Q]$ satisfies $|Z|\ge n/\sqrt s$, then, for the smoothing $\mathcal G=G\cup R$ with $\lambda=\beta\ln n$,
--   $$
--   \mathbb P\Big[\operatorname{diam}(\mathcal G[Z])>200\sqrt{\ln n}\Big]\le 3\exp\Big(-\frac{\lambda\sqrt s}{4c'}\Big).
--   $$
--   In particular, for every $d>0$ and all large $n$, the right-hand side is smaller than $n^{-d}$, uniformly in $s\ge e^{0.49\sqrt{\ln n}}$.
--
--   Cases (1) and (2a) of the analysis apply it with $(F,Q,s)=(G,H_0,B_0)$ and $(G[L_0],Q,t)$.
--
--   Differences from the source:
--   - generalization: c′ is the constant of Lemma 2.2 → any c′ ≥ 1 for which the bound of Lemma 2.2 holds (ERDiamBound c′); reason: includes the paper's constant (c′ = 1024, App. A); the conclusion is claimed for each such c′
--   - encoding: F a fixed subgraph of G with Q ⊆ V(F) → F ≤ G as graphs on the same vertex set Fin n; reason: a subgraph on fewer vertices is the same graph with isolated extra vertices; degrees and Z = N²_F[Q] are unchanged
--   - encoding: diam(𝒢[Z]) > 200√ln n → ⌊200√ln n⌋ < ediam of 𝒢 induced on Z (⊤ when disconnected); reason: a diameter is an integer or ∞, so the two events coincide
--   - reading: for all sufficiently large n (depending only on β) → ∃ n0 depending on c′ and β, before G, F, s and Q; reason: the proof's conditions involve only n and β (p.14); c′ is a fixed constant
--   - reading: the right-hand side is smaller than every fixed inverse polynomial in n → ∀ d > 0, ∃ n1, ∀ n ≥ n1, ∀ s ≥ e^{0.49√ln n}: 3exp(−λ√s/(4c′)) < n^{−d}; reason: uniform in s, as the proof's last line shows
--   - encoding: random edges with probability p = λ/n → coins with probability min(1, β ln n/n) on all pairs, 𝒢 = G ⊔ {pairs with coin true}; reason: same law for large n; coins on edges of G change nothing
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 3.1, p.12; proof pp.13–14 (PDF pp.14–16)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_ERDiamBound
import Definitions.Def_SmoothedMIS_smoothLaw
import Definitions.Def_SmoothedMIS_B0

open MeasureTheory

namespace SmoothedMIS

/-- **Lemma 3.1 (Smoothed diameter of a large two-hop neighborhood)** (Dey, Dufoulon, Moses Jr.,
Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 3.1,
p.12). Let `F` be a fixed subgraph of `G`, `s` an integer with `e^{0.49√ln n} ≤ s ≤ B0`, and
`Q ⊆ V(F)` a fixed set of seeds with `deg_F(v) > s` for every `v ∈ Q`. If `Z = N²_F[Q]`
satisfies `|Z| ≥ n/√s`, then, for all sufficiently large `n` (depending only on `β`),
`P[diam(𝒢[Z]) > 200√ln n] ≤ 3 exp(−λ√s/(4c'))`, where `c'` is the constant of Lemma 2.2. In
particular, the right-hand side is smaller than every fixed inverse polynomial in `n`.

**Formalization Note**
* `c'` is any constant `≥ 1` for which the bound of Lemma 2.2 holds (`ERDiamBound c'`), which
  includes the paper's constant; `n0` depends on `c'` and `β` only, not on `G, F, s, Q`.
* `𝒢 = G ∪ R` is `addSmooth G ω` under `smoothLaw n β`; `diam(𝒢[Z])` is the `ediam` of the
  induced graph (`∞` if disconnected), and `diam > 200√ln n` is `⌊200√ln n⌋ < diam`.
* `F` is a subgraph of `G` on the same vertex set (a subgraph on fewer vertices is the same
  graph with isolated extra vertices; degrees and `Z` are unchanged).
* The "in particular" clause is uniform in `s ≥ e^{0.49√ln n}`. -/
theorem lemma_3_1 :
    ∀ c' : ℝ, 1 ≤ c' → ERDiamBound c' → ∀ β : ℝ, 1 ≤ β →
      (∃ n0 : ℕ, ∀ n ≥ n0, ∀ G F : SimpleGraph (Fin n), F ≤ G →
        ∀ s : ℕ, Real.exp (0.49 * Real.sqrt (Real.log n)) ≤ s → s ≤ B0 n →
        ∀ Q : Set (Fin n), (∀ v ∈ Q, s < deg F v) →
        (n : ℝ) / Real.sqrt s ≤ (twoHop F Q).ncard →
          (smoothLaw n β {ω | ((⌊200 * Real.sqrt (Real.log n)⌋₊ : ℕ) : ℕ∞) <
              ((addSmooth G ω).induce (twoHop F Q)).ediam}).toReal
            ≤ 3 * Real.exp (-(lam n β * Real.sqrt s) / (4 * c'))) ∧
      ∀ d : ℝ, 0 < d → ∃ n1 : ℕ, ∀ n ≥ n1, ∀ s : ℕ,
        Real.exp (0.49 * Real.sqrt (Real.log n)) ≤ s →
          3 * Real.exp (-(lam n β * Real.sqrt s) / (4 * c')) < (n : ℝ) ^ (-d) := by sorry

end SmoothedMIS
