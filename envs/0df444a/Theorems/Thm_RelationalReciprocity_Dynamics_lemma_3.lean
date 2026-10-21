-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_lemma_3
-- name    : RelationalReciprocity.Dynamics.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:33.466001+00:00
-- url     : https://prove2.me/theorems/d1b8e9cc-5838-411b-a6e5-fec137152245
-- title:
--   Lemma 3, p. 18 — with (DE) slack, a positive wage is optimal iff η > η̄ = √(1/θ³)
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold, and set $\bar\eta=\sqrt{1/\theta^3}$; then $\bar\eta>0$.
--
--   1. If $\eta>\bar\eta$, the first-best pairs (maximizers of $\pi$ over $e,w\ge0$ without (DE)) are exactly
--   $$
--   e=\frac{1+\eta^2\theta^3}{2\eta\theta},\qquad w=\frac{(\eta^2\theta^3-1)^2}{4\eta^3\theta^3},
--   $$
--   and this wage is strictly positive.
--   2. If $\eta\le\bar\eta$, the first-best pairs are exactly $e=\sqrt\theta$, $w=0$.
--   3. For every bound $K$ at which (DE) does not bind (some first-best pair satisfies $b(e,w)\le K$), the optimal pairs of the period problem with bound $K$ are exactly the first-best pairs.
--
--   Hence, when the dynamic enforcement constraint does not bind, a strictly positive wage is optimal for $\eta>\bar\eta$ and the optimal wage is zero for $\eta\le\bar\eta$.
--
--   **Formalization Note.** The paper states "there exists $\bar\eta>0$"; the statement uses the value $\bar\eta=\sqrt{1/\theta^3}$ from the paper's proof. The paper's "period $t<T$" is replaced by an arbitrary bound $K$ at which (DE) is slack. The hypothesis $\eta>0$ is added because the closed forms divide by $\eta$.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 18 (PDF 20), Lemma 3; closed forms from its proof, p. 40 (PDF 42)

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Lemma 3, p. 18, with the closed forms of its proof, p. 40: with `η̄ = √(1/θ³) > 0`, the
first-best pair is `e = (1+η²θ³)/(2ηθ)`, `w = (η²θ³−1)²/(4η³θ³) > 0` if `η > η̄`, and
`e = √θ`, `w = 0` if `η ≤ η̄`; when (DE) does not bind, the optimal pairs are the first-best pairs. -/
theorem lemma_3 (P : Params) (hP : P.Standing) (hη : 0 < P.η) :
    0 < etabar P ∧
    (etabar P < P.η → ∀ e w : ℝ, IsFirstBest P e w ↔
      e = (1 + P.η ^ 2 * P.θ ^ 3) / (2 * P.η * P.θ) ∧
      w = (P.η ^ 2 * P.θ ^ 3 - 1) ^ 2 / (4 * P.η ^ 3 * P.θ ^ 3)) ∧
    (etabar P < P.η → 0 < (P.η ^ 2 * P.θ ^ 3 - 1) ^ 2 / (4 * P.η ^ 3 * P.θ ^ 3)) ∧
    (P.η ≤ etabar P → ∀ e w : ℝ, IsFirstBest P e w ↔ e = Real.sqrt P.θ ∧ w = 0) ∧
    (∀ K e w : ℝ, DESlack P K → (IsOptimal P K e w ↔ IsFirstBest P e w)) := by sorry

end RelationalReciprocity.Dynamics
