-- Prove2me | Theorems.Thm_UnderstandingML_rademacher_generalization
-- name    : UnderstandingML.rademacher_generalization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:41:37.427314+00:00
-- url     : https://prove2.me/theorems/53d3bb92-de67-42cf-8fab-4c1c85843349
-- title:
--   Theorem 26.5: for |ℓ| ≤ c, w.p. ≥ 1−δ, ∀h∈H: L_D(h) − L_S(h) ≤ 2E R + c√(2ln(2/δ)/m); ≤ 2R(ℓ∘H∘S) + 4c√(2ln(4/δ)/m); and L_D(ERM) − L_D(h⋆) ≤ 2R(ℓ∘H∘S) + 5c√(2ln(8/δ)/m)
-- statement:
--   **Theorem 26.5.** Assume that for all $z$ and $h \in H$ we have that $|\ell(h, z)| \le c$. Then,
--   1. With probability of at least $1 - \delta$, for all $h \in H$, $L_D(h) - L_S(h) \le 2\,\mathbb{E}_{S' \sim D^m}R(\ell \circ H \circ S') + c\sqrt{\frac{2\ln(2/\delta)}{m}}$. In particular, this holds for $h = \mathrm{ERM}_H(S)$.
--   2. With probability of at least $1 - \delta$, for all $h \in H$, $L_D(h) - L_S(h) \le 2R(\ell \circ H \circ S) + 4c\sqrt{\frac{2\ln(4/\delta)}{m}}$. In particular, this holds for $h = \mathrm{ERM}_H(S)$.
--   3. For any $h^\star$, with probability of at least $1 - \delta$, $L_D(\mathrm{ERM}_H(S)) - L_D(h^\star) \le 2R(\ell \circ H \circ S) + 5c\sqrt{\frac{2\ln(8/\delta)}{m}}$.
--
--   Formally: each part bounds the probability of the failure event by $\delta$; part 3 for every ERM learner and $h^\star \in H$. The loss is bounded by $c$ and measurable, $H$ is nonempty, $m \ge 1$, and the maps $S \mapsto \operatorname{Rep}_D(F, S)$ and $S \mapsto R(F \circ S)$ are measurable (Remark 3.1).
--
--   **The double-sample measurability.** Besides $S \mapsto \mathrm{Rep}_D(\ell\circ H, S)$ and $S \mapsto R(\ell\circ H\circ S)$, the item assumes that $(S, S') \mapsto \sup_{h \in H}(L_{S'}(h) - L_S(h))$ is measurable, because the proof of Lemma 26.2 integrates it. Swapping $z_i$ and $z'_i$ preserves $D^m \otimes D^m$, so $\mathbb{E}[\sup_h(L_{S'} - L_S)]$ equals its average over sign vectors $\sigma$. That average is at most $\mathbb{E}[R(S) + R(S')]$ pointwise. Without this hypothesis the per-$\sigma$ suprema need not be measurable, and their upper integrals can exceed the integral of their average $R(S)$, so the argument does not close. The hypothesis holds whenever the loss class has a countable pointwise-dense subclass, as in Theorems 26.12-26.15.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1 pp. 378-379, Theorem 26.5 with its proof

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 26.5** (p. 378). Assume that for all `z` and `h ∈ H` we have `|ℓ(h, z)| ≤ c`. Then:
1. with probability at least `1 − δ`, for all `h ∈ H`,
   `L_D(h) − L_S(h) ≤ 2 E_{S' ∼ D^m} R(ℓ ∘ H ∘ S') + c √(2 ln(2/δ)/m)`;
2. with probability at least `1 − δ`, for all `h ∈ H`,
   `L_D(h) − L_S(h) ≤ 2 R(ℓ ∘ H ∘ S) + 4c √(2 ln(4/δ)/m)`;
3. for any `h⋆`, with probability at least `1 − δ`,
   `L_D(ERM_H(S)) − L_D(h⋆) ≤ 2 R(ℓ ∘ H ∘ S) + 5c √(2 ln(8/δ)/m)`.
Each holds in particular for `h = ERM_H(S)`. Hypotheses as in Lemma 26.2; part 3 for an ERM
learner and `h⋆ ∈ H`. -/
theorem rademacher_generalization {Z Hyp : Type*} [MeasurableSpace Z]
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (hH : H.Nonempty) (c : ℝ)
    (hc : ∀ h ∈ H, ∀ z, |loss h z| ≤ c) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m)
    (hrep : Measurable (fun S : Fin m → Z ↦ representativeness loss H D S))
    (hrad : Measurable (fun S : Fin m → Z ↦ rademacher (evalSet (lossClass loss H) S)))
    (hdbl : Measurable (fun p : (Fin m → Z) × (Fin m → Z) ↦
      ⨆ h : H, (empRisk loss p.2 (h : Hyp) - empRisk loss p.1 (h : Hyp))))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (iidLaw D m {S | ∃ h ∈ H,
      2 * (∫ S', rademacher (evalSet (lossClass loss H) S') ∂(iidLaw D m)) +
        c * Real.sqrt (2 * Real.log (2 / δ) / m) < risk loss D h - empRisk loss S h} ≤
      ENNReal.ofReal δ) ∧
    (iidLaw D m {S | ∃ h ∈ H,
      2 * rademacher (evalSet (lossClass loss H) S) + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / m) <
        risk loss D h - empRisk loss S h} ≤ ENNReal.ofReal δ) ∧
    (∀ (A : Learner Z Hyp), IsERMLearner loss H A → ∀ hstar ∈ H,
      iidLaw D m {S | 2 * rademacher (evalSet (lossClass loss H) S) +
        5 * c * Real.sqrt (2 * Real.log (8 / δ) / m) < risk loss D (A m S) - risk loss D hstar} ≤
      ENNReal.ofReal δ) := by sorry

end UnderstandingML
