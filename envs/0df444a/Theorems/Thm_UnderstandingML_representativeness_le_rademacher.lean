-- Prove2me | Theorems.Thm_UnderstandingML_representativeness_le_rademacher
-- name    : UnderstandingML.representativeness_le_rademacher
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:38:06.048237+00:00
-- url     : https://prove2.me/theorems/c352c2cb-9000-4caa-978a-3c356310c098
-- title:
--   Lemma 26.2: E_S[Rep_D(F, S)] ≤ 2 E_S R(F ∘ S) for F = ℓ ∘ H
-- statement:
--   **Lemma 26.2.** $\mathbb{E}_{S \sim D^m}[\operatorname{Rep}_D(F, S)] \le 2\,\mathbb{E}_{S \sim D^m}R(F \circ S)$. The loss is bounded by $c$ and measurable, $H$ is nonempty, $m \ge 1$, and the maps $S \mapsto \operatorname{Rep}_D(F, S)$ and $S \mapsto R(F \circ S)$ are measurable (Remark 3.1).
--
--   **The double-sample measurability.** Besides $S \mapsto \mathrm{Rep}_D(\ell\circ H, S)$ and $S \mapsto R(\ell\circ H\circ S)$, the item assumes that $(S, S') \mapsto \sup_{h \in H}(L_{S'}(h) - L_S(h))$ is measurable, because the proof of Lemma 26.2 integrates it. Swapping $z_i$ and $z'_i$ preserves $D^m \otimes D^m$, so $\mathbb{E}[\sup_h(L_{S'} - L_S)]$ equals its average over sign vectors $\sigma$. That average is at most $\mathbb{E}[R(S) + R(S')]$ pointwise. Without this hypothesis the per-$\sigma$ suprema need not be measurable, and their upper integrals can exceed the integral of their average $R(S)$, so the argument does not close. The hypothesis holds whenever the loss class has a countable pointwise-dense subclass, as in Theorems 26.12-26.15.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1 pp. 376-377, Lemma 26.2 with its proof (symmetrization)

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 26.2** (p. 376). `E_{S ∼ D^m}[Rep_D(F, S)] ≤ 2 E_{S ∼ D^m} R(F ∘ S)` for `F = ℓ ∘ H`.
The loss is bounded by `c` and measurable, `H` is nonempty, and the two random variables
`S ↦ Rep_D(F, S)` and `S ↦ R(F ∘ S)` are measurable (Remark 3.1), as is the double-sample
supremum `(S, S′) ↦ sup_h (L_{S′}(h) − L_S(h))` that the symmetrization integrates. -/
theorem representativeness_le_rademacher {Z Hyp : Type*} [MeasurableSpace Z]
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty) (c : ℝ)
    (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m)
    (hrep : Measurable (fun S : Fin m → Z ↦ representativeness loss H D S))
    (hrad : Measurable (fun S : Fin m → Z ↦ rademacher (evalSet (lossClass loss H) S)))
    (hdbl : Measurable (fun p : (Fin m → Z) × (Fin m → Z) ↦
      ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp)))) :
    ∫ S, representativeness loss H D S ∂(iidLaw D m) ≤
      2 * ∫ S, rademacher (evalSet (lossClass loss H) S) ∂(iidLaw D m) := by sorry

end UnderstandingML
