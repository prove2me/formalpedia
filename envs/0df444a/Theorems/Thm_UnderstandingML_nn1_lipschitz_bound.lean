-- Prove2me | Theorems.Thm_UnderstandingML_nn1_lipschitz_bound
-- name    : UnderstandingML.nn1_lipschitz_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:55:46.685987+00:00
-- url     : https://prove2.me/theorems/f7c7340d-174c-4639-8420-d0d036a2a6c8
-- title:
--   Lemma 19.1: for c-Lipschitz η on [0,1]^d, E_S[L_D(h_S)] ≤ 2 L_D(h⋆) + c E_{S,x}[‖x − x_{π₁(x)}‖] for the 1-NN rule
-- statement:
--   **Lemma 19.1.** Let $X = [0,1]^d$, $Y = \{0,1\}$, and $D$ be a distribution over $X \times Y$ for which the conditional probability function, $\eta$, is a $c$-Lipschitz function. Let $S = (x_1, y_1), \dots, (x_m, y_m)$ be an i.i.d. sample and let $h_S$ be its corresponding 1-NN hypothesis. Let $h^\star$ be the Bayes optimal rule for $\eta$. Then
--   $$\mathbb{E}_{S \sim D^m}[L_D(h_S)] \le 2L_D(h^\star) + c\,\mathbb{E}_{S \sim D^m, x \sim D}\big[\|x - x_{\pi_1(x)}\|\big].$$
--
--   Formally: $D = $ `condLaw DX η` with $\eta$ valued in $[0,1]$, $h$ any 1-NN rule (any tie-breaking), measurable in $(S, x)$, and $m \ge 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.2.1 p. 260, Lemma 19.1

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 19.1** (p. 260). Let `X = [0,1]^d`, `Y = {0,1}`, and `D` be a distribution over
`X × Y` for which the conditional probability function `η` is a `c`-Lipschitz function. Let
`S = (x₁, y₁), …, (x_m, y_m)` be an i.i.d. sample and let `h_S` be its corresponding 1-NN
hypothesis. Let `h⋆` be the Bayes optimal rule for `η`. Then
`E_{S ∼ D^m}[L_D(h_S)] ≤ 2 L_D(h⋆) + c E_{S ∼ D^m, x ∼ D}[‖x − x_{π₁(x)}‖]`.
Here `D = condLaw D_X η`, the rule is any 1-NN rule, measurable in `(S, x)`, and `m ≥ 1`. -/
theorem nn1_lipschitz_bound (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsNN1Rule h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : 0 < m) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      2 * risk loss01 (condLaw DX η) (bayesRule η) +
        c * ∫ p, nnDist p.1 p.2 ∂((iidLaw (condLaw DX η) m).prod DX) := by sorry

end UnderstandingML
