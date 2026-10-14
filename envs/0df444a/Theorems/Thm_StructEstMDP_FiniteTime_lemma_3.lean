-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_lemma_3
-- name    : StructEstMDP.FiniteTime.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:12.925067+00:00
-- url     : https://prove2.me/theorems/5edf400b-6c86-4476-890b-c048fd58d7f4
-- title:
--   Lemma 3, p. 11 (constants p. 35) — Q_θ is L_r/(1−γ)-Lipschitz in θ, and ∇L̂ is L_c-Lipschitz for every constant C_d of Lemma 5
-- statement:
--   Let $(\mathcal S,\mathcal A,P,\rho,\gamma)$ be a finite MDP with $\gamma\in[0,1)$ satisfying Assumption 2, let the reward satisfy Assumptions 1 and 3 with constants $C_r,L_r,L_g$, and let $\mathcal D$ be a nonempty dataset. Write $L_q=L_r/(1-\gamma)$.
--
--   1. For all $\theta_1,\theta_2$ and all $(s,a)$, the soft-optimal Q-functions satisfy
--   $$|Q_{\theta_1}(s,a)-Q_{\theta_2}(s,a)|\le L_q\|\theta_1-\theta_2\|.\qquad(20a)$$
--   2. For every $C_d>0$ with which the conclusion of Lemma 5 holds, and all $\theta_1,\theta_2$,
--   $$\|\nabla_\theta\widehat L(\theta_1;\mathcal D)-\nabla_\theta\widehat L(\theta_2;\mathcal D)\|\le L_c\|\theta_1-\theta_2\|,\qquad L_c=\frac{2L_qL_rC_d\sqrt{|\mathcal S|\cdot|\mathcal A|}}{1-\gamma}+\frac{2L_g}{1-\gamma}.\qquad(20b)$$
--
--   These are the two Lipschitz properties on which the two-timescale analysis rests: (20a) controls the drift of the target $Q_{\theta_k}$, and (20b) is the smoothness of the upper-level objective used in the ascent inequality (46).
--
--   **Formalization Note** The page states the existence of positive constants $L_q,L_c$ and gives their values in §17 (p. 35); the Lean states the explicit values, which is stronger. (20b) is stated for every constant $C_d$ satisfying Lemma 5's bound, which is how the proof of Theorem 1 uses it.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 11, Lemma 3, (20a)–(20b); constants §17, p. 35; Remark 3, p. 12

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Lemma 3, p. 11, with the constants of §17, p. 35: (20a) `Q_θ` is `L_q`-Lipschitz in `θ`
with `L_q = L_r/(1−γ)`; (20b) for every constant `C_d` of Lemma 5, `∇_θ L̂(·; D)` is
`L_c`-Lipschitz with `L_c = 2 L_q L_r C_d √(|S|·|A|)/(1−γ) + 2 L_g/(1−γ)`. -/
theorem lemma_3 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hρ : IsDist ρ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h2 : Assumption2 P)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Cr Lr Lg : ℝ)
    (h1 : Assumption1 r Cr) (h3 : Assumption3 r Lr Lg)
    {m : ℕ} (D : Fin m → Traj S A) (hm : 0 < m) :
    (∀ (θ₁ θ₂ : EuclideanSpace ℝ (Fin p)) (s : S) (a : A),
        |optQ P γ r θ₁ s a - optQ P γ r θ₂ s a| ≤ Lr / (1 - γ) * ‖θ₁ - θ₂‖) ∧
      ∀ Cd : ℝ, 0 < Cd →
        (∀ w w' : S → A → ℝ,
          tvDist (visitation P γ ρ (softmax w)) (visitation P γ ρ (softmax w')) ≤
            Cd * frobNorm (w - w')) →
        ∀ θ₁ θ₂ : EuclideanSpace ℝ (Fin p),
          ‖gradient (Lhat P γ ρ r D) θ₁ - gradient (Lhat P γ ρ r D) θ₂‖ ≤
            (2 * (Lr / (1 - γ)) * Lr * Cd * Real.sqrt (Fintype.card S * Fintype.card A) / (1 - γ)
              + 2 * Lg / (1 - γ)) * ‖θ₁ - θ₂‖ := by sorry

end StructEstMDP.FiniteTime
