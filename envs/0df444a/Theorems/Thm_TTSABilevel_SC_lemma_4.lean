-- Prove2me | Theorems.Thm_TTSABilevel_SC_lemma_4
-- name    : TTSABilevel.SC.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:24.189584+00:00
-- url     : https://prove2.me/theorems/ad57c949-d0ba-48c0-b322-5515a9651b10
-- title:
--   Lemma 4 (29): explicit outer-error recursion bound
-- statement:
--   Under Assumptions 1–3 and the strongly convex outer setting of Theorem 1, let $\Delta_x^k=\mathbb E\|x^k-x^\star\|^2$, and suppose $b_k^2\le\widetilde c_b\alpha_{k+1}$. With $G^{(2)}_{m:n}=\prod_{i=m}^n(1-\alpha_i\mu_\ell)$, Lemma 4 states, for every $k\ge1$,
--
--   $$
--   \Delta_x^{k+1}\le G^{(2)}_{0:k}\Delta_x^0+
--   \left[\frac{4\widetilde c_b}{\mu_\ell^2}+\frac{2\widetilde\sigma_f^2+6b_0^2}{\mu_\ell}\right]\alpha_k+
--   \left[\frac{2L^2}{\mu_\ell}+3\alpha_0L^2\right]
--   \sum_{j=0}^k\alpha_jG^{(2)}_{j+1:k}\Delta_y^{j+1}.
--   $$
--
--   The bound leaves the inner tracking errors visible so they can be bounded by (55).
--
--   **Formalization Note** A strengthened consecutive-step condition, $\alpha_{k-1}\le(1+\mu_\ell\alpha_k/2)\alpha_k$, is stated explicitly because the proof’s use of Lemma 10 with $q=2$ requires it; (20a) prints the weaker coefficient $3/4$.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 13, Lemma 4 (29); pp. 21–22, App. A.2

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

open MeasureTheory

namespace TTSABilevel.SC

theorem lemma_4 {d1 d2 : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Set (E1 d1)) (f g : E1 d1 → E2 d2 → ℝ)
    (ystar : E1 d1 → E2 d2) (proj : E1 d1 → E1 d1)
    (α β : ℕ → ℝ) (x0 : E1 d1) (y0 : E2 d2)
    (x : ℕ → Ω → E1 d1) (y : ℕ → Ω → E2 d2)
    (hg : ℕ → Ω → E2 d2) (hf B : ℕ → Ω → E1 d1)
    (Lfx Lfy Lfybar Cfy Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy σg σf : ℝ)
    (b : ℕ → ℝ) (μℓ c0 c1 cb : ℝ) (xstar : E1 d1)
    (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (hf1 : ContDiff ℝ 1 (Function.uncurry f))
    (h1 : Asm1 f X Lfx Lfy Lfybar Cfy)
    (h2 : Asm2 g X Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy)
    (hinner : IsInnerSol g X ystar)
    (hrun : IsTTSARun P X proj α β x0 y0 x y hg hf)
    (h3 : Asm3 P f g ystar x y hg hf B σg σf b)
    (hbounded : BddAbove ((fun z : E1 d1 => ‖gradEll f g ystar z‖ ^ 2) '' X))
    (hμℓ : 0 < μℓ)
    (hweak : WeaklyConvexWith X (ell f ystar) (gradEll f g ystar) μℓ)
    (hxstar : xstar ∈ X) (hoptimal : ∀ z ∈ X, ell f ystar xstar ≤ ell f ystar z)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hcb : 0 ≤ cb)
    (hαpos : ∀ k, 0 < α k) (hβpos : ∀ k, 0 < β k)
    (hαmono : Antitone α) (hβmono : Antitone β)
    (hαβ : ∀ k, α k ≤ c0 * (β k) ^ ((3 : ℝ) / 2))
    (hβα : ∀ k, β k ≤ c1 * (α k) ^ ((2 : ℝ) / 3))
    (hβratio : ∀ k, 1 ≤ k → β (k - 1) ≤ (1 + β k * μg / 8) * β k)
    (hαratio : ∀ k, 1 ≤ k → α (k - 1) ≤ (1 + 3 * α k * μℓ / 4) * α k)
    (hαratio_half : ∀ k, 1 ≤ k → α (k - 1) ≤ (1 + α k * μℓ / 2) * α k)
    (hαmax : ∀ k, α k ≤ 1 / μℓ)
    (hβmax1 : ∀ k, β k ≤ 1 / μg)
    (hβmax2 : ∀ k, β k ≤ μg / (Lg ^ 2 * (1 + σg ^ 2)))
    (hβmax3 : ∀ k, β k ≤ μg ^ 2 /
      (48 * c0 ^ 2 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 *
        (Lyconst Cgxy μg) ^ 2))
    (hscale : ∀ k, 8 * μℓ * α k ≤ μg * β k)
    (hcbias : ∀ k, b k ^ 2 ≤ cb * α (k + 1)) :
    ∀ k : ℕ, 1 ≤ k →
      Dx P x xstar (k + 1) ≤
        G2 α μℓ 0 k * Dx P x xstar 0 +
          (4 * cb / μℓ ^ 2 +
            (2 * sigTilde2 σf X f g ystar + 6 * b 0 ^ 2) / μℓ) * α k +
          (2 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 / μℓ +
            3 * α 0 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2) *
            (∑ j ∈ Finset.range (k + 1),
              α j * G2 α μℓ (j + 1) k * Dy P ystar x y (j + 1)) := by sorry

end TTSABilevel.SC
