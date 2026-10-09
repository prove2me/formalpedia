-- Prove2me | Theorems.Thm_TTSABilevel_SC_theorem_1_explicit
-- name    : TTSABilevel.SC.theorem_1_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:51.031465+00:00
-- url     : https://prove2.me/theorems/48f98bca-59d9-49cf-a843-d93f46df4118
-- title:
--   Theorem 1 in explicit form: strongly convex TTSA error bounds
-- statement:
--   Let $X$ be closed and convex, let $y^\star(x)$ solve the strongly convex inner problem, and let TTSA follow Algorithm 1 under Assumptions 1–3 and the step-size conditions (20a)–(20b). Suppose the outer objective $\ell(x)=f(x,y^\star(x))$ has modulus $\mu_\ell>0$, $x^\star$ is optimal, and $b_k^2\le\widetilde c_b\alpha_{k+1}$. Put $\Delta_x^k=\mathbb E\|x^k-x^\star\|^2$ and $\Delta_y^k=\mathbb E\|y^k-y^\star(x^{k-1})\|^2$. Then, for every $k\ge0$,
--
--   $$
--   \Delta_y^{k+1}\le G^{(1)}_{0:k}\Delta_y^0+C_y^{(1)}\beta_k,
--   $$
--
--   and
--
--   $$
--   \begin{aligned}
--   \Delta_x^{k+1}\le{}&G^{(2)}_{0:k}\left\{\Delta_x^0+\left[\frac{2L^2}{\mu_\ell^2}+\frac{3\alpha_0L^2}{\mu_\ell}\right]\Delta_y^0\right\}\\
--   &+\frac{2}{\mu_\ell}\left[\frac{2\widetilde c_b}{\mu_\ell}+\widetilde\sigma_f^2+3b_0^2\right]\alpha_k\\
--   &+\frac{2c_1}{\mu_\ell}\left[\frac{2L^2}{\mu_\ell}+3\alpha_0L^2\right]C_y^{(1)}\alpha_k^{2/3}.
--   \end{aligned}
--   $$
--
--   Here $L,L_y$ are exactly (13), $\widetilde\sigma_f^2$ is (14), $C_y^{(1)}$ is (55), and the products $G^{(1)},G^{(2)}$ are (48). These are the paper’s explicit bounds underlying Theorem 1’s rate statement.
--
--   **Formalization Note** Step sizes are positive and nonincreasing. In addition to (20a), the statement includes $\alpha_{k-1}\le(1+\mu_\ell\alpha_k/2)\alpha_k$: the printed factor $3/4$ does not support the proof’s use of Lemma 10 with $q=2$. Conditional moments use the iterates’ generated sigma-algebras, and the boundedness of $\widetilde\sigma_f^2$ is explicit. The identity $x^{-1}=x^0$ is used in $\Delta_y^0$.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 10, Theorem 1 (20a)–(21); p. 21, App. A.1, (55); p. 22, App. A.3, display after (59)

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

open MeasureTheory

namespace TTSABilevel.SC

theorem theorem_1_explicit {d1 d2 : ℕ} {Ω : Type*} [MeasurableSpace Ω]
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
    ∀ k : ℕ,
      (Dy P ystar x y (k + 1) ≤
        G1 β μg 0 k * Dy P ystar x y 0 +
          Cy1 μg σg c0 Cgxy σf b X f g ystar * β k) ∧
      (Dx P x xstar (k + 1) ≤
        G2 α μℓ 0 k *
          (Dx P x xstar 0 +
            (2 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 / μℓ ^ 2 +
              3 * α 0 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 / μℓ) *
              Dy P ystar x y 0) +
        2 / μℓ *
          (2 * cb / μℓ + sigTilde2 σf X f g ystar + 3 * b 0 ^ 2) * α k +
        2 * c1 / μℓ *
          (2 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 / μℓ +
            3 * α 0 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2) *
          Cy1 μg σg c0 Cgxy σf b X f g ystar * (α k) ^ ((2 : ℝ) / 3)) := by sorry

end TTSABilevel.SC
