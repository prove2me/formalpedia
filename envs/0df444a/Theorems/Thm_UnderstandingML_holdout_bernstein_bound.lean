-- Prove2me | Theorems.Thm_UnderstandingML_holdout_bernstein_bound
-- name    : UnderstandingML.holdout_bernstein_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:59:59.644315+00:00
-- url     : https://prove2.me/theorems/b4c9d875-9ae5-4c17-b2bd-19520f3fe11b
-- title:
--   Lemma 30.1: for a hypothesis built from T and evaluated on the independent V, L_D(h_T) − L_V(h_T) < √(2 L_V(h_T) log(1/δ)/|V|) + 4 log(1/δ)/|V| w.p. ≥ 1 − δ
-- statement:
--   **Lemma 30.1.** Assume that the range of the loss function is $[0,1]$. Then, for $h_T$ built from a sample $T$ of $k$ examples and $V$ a fresh sample of $m - k$ examples,
--   $$P\Big[L_D(h_T) - L_V(h_T) \ge \sqrt{\frac{2L_V(h_T)\log(1/\delta)}{|V|}} + \frac{4\log(1/\delta)}{|V|}\Big] \le \delta.$$
--
--   Formally: $T$ is the first $k$ and $V$ the last $n = |V| \ge 1$ examples of a sample of size $k + n$; $(T, z) \mapsto \ell(B(T), z)$ is measurable; $\delta \in (0,1)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.1 p. 410, Lemma 30.1 (from Bernstein's inequality, Lemma B.10)

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 30.1** (p. 410). Assume that the range of the loss function is `[0, 1]`. Then, for a
hypothesis `h_T` built from the first `k` examples and evaluated on the remaining `|V| = m − k`,
`P[L_D(h_T) − L_V(h_T) ≥ √(2 L_V(h_T) log(1/δ)/|V|) + 4 log(1/δ)/|V|] ≤ δ`.
`|V| ≥ 1`, `δ ∈ (0, 1)`, and `(T, z) ↦ ℓ(B(T), z)` is measurable. -/
theorem holdout_bernstein_bound {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (k n : ℕ) (hn : 0 < n) (B : (Fin k → Z) → Hyp)
    (hB : Measurable (fun p : (Fin k → Z) × Z ↦ loss (B p.1) p.2)) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    iidLaw D (k + n) {S | Real.sqrt (2 * ((∑ j : Fin n, loss (B (fun i ↦ S (Fin.castAdd n i)))
          (S (Fin.natAdd k j))) / n) * Real.log (1 / δ) / n) + 4 * Real.log (1 / δ) / n ≤
        risk loss D (B (fun i ↦ S (Fin.castAdd n i))) -
          (∑ j : Fin n, loss (B (fun i ↦ S (Fin.castAdd n i))) (S (Fin.natAdd k j))) / n} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
