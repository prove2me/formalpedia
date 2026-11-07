-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_4_6
-- name    : SmoothedMIS.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:57.920061+00:00
-- url     : https://prove2.me/theorems/5bcfdce3-dea8-49b8-9c5d-4130f0f5e544
-- title:
--   Lemma 4.6 — few random edges per vertex; $L_0\subseteq V_{lo}$ and $\mathcal A\subseteq V_{hi}\subseteq H_0$
-- statement:
--   Let $\beta\ge1$ and $n\ge1$, and let $E$ be the event that every vertex has at most $2\lambda$ incident edges in $R$. Then
--   $$
--   \mathbb P[E^c]\le n e^{-\lambda/3}=n^{1-\beta/3}.
--   $$
--   Moreover, whenever $E$ holds, $L_0\subseteq V_{lo}$, and hence $\mathcal A\subseteq V_{hi}\subseteq H_0$.
--
--   The lemma links the degree classes of the algorithm (in $\mathcal G$) to those of the base graph, and $\mathbb P[E^c]$ is one term of every union bound of §4.2.1.
--
--   Differences from the source:
--   - encoding: the probabilities over the random edges R and the marks of Step 1 → the analysis law: smoothing coins on all pairs with probability min(1, β ln n/n) and independent mark coins κ_uv on all pairs with probability θ (clamped to [0,1]); reason: p.25 states that the per-pair coins have the same distribution as the algorithm; coins on edges of G change nothing; the clamps are the identity for large n
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 4.6, p.20; proof p.21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_SmoothedMIS_testSet

open MeasureTheory

namespace SmoothedMIS

/-- **Lemma 4.6 (Few random edges per vertex)** (Dey, Dufoulon, Moses Jr., Pandurangan,
*Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 4.6, p.20). Let `E`
be the event that every vertex has at most `2λ` incident edges in `R`. Then `E` fails with
probability at most `ne^{−λ/3} = n^{1−β/3}`. Moreover, if `E` holds, we have `L0 ⊆ V_lo`, and
hence `𝒜 ⊆ V_hi ⊆ H0`.

**Formalization Note** For every `β ≥ 1` and every `n ≥ 1`, under the analysis law
`anaLaw n β` (smoothing coins with probability `min 1 (β ln n/n)`, mark coins with probability
`θ`). The inclusions hold pointwise on `E`. -/
theorem lemma_4_6 (β : ℝ) (hβ : 1 ≤ β) (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    (anaLaw n β {ω | ¬ EventE β G ω.1}).toReal ≤ n * Real.exp (-(lam n β) / 3) ∧
    (n : ℝ) * Real.exp (-(lam n β) / 3) = (n : ℝ) ^ (1 - β / 3) ∧
    ∀ ω : Coins n, EventE β G ω.1 →
      L0 G ⊆ Vlo β G ω.1 ∧ activeSet β G ω ⊆ Vhi β G ω.1 ∧ Vhi β G ω.1 ⊆ H0 G := by sorry

end SmoothedMIS
