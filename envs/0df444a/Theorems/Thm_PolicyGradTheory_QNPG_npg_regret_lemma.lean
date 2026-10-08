-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_npg_regret_lemma
-- name    : PolicyGradTheory.QNPG.npg_regret_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:54.13522+00:00
-- url     : https://prove2.me/theorems/8c003380-d453-4b21-b80f-fad5271573d5
-- title:
--   Lemma 6.2, pp. 37–38 — deterministic NPG regret bound
-- statement:
--   Consider a policy class πθ with strictly positive action probabilities whose log probabilities are differentiable and β-smooth, a comparison policy π̃, a start distribution ρ, and an update $\theta^{(t+1)}=\theta^{(t)}+\eta w^{(t)}$. Suppose π⁽⁰⁾ is uniform, η is positive, and each direction has norm at most W. Let
--
--   $$
--   \mathrm{err}_t=\mathbb E_{s\sim d^{\tilde\pi}_\rho}
--     \mathbb E_{a\sim\tilde\pi(\cdot\mid s)}
--     [A^{(t)}(s,a)-w^{(t)}\cdot\nabla_\theta\log\pi^{(t)}(a\mid s)].
--   $$
--
--   For every positive horizon T, some $t<T$ satisfies
--
--   $$
--   V^{\tilde\pi}(\rho)-V^{(t)}(\rho)\le
--     \frac{1}{1-\gamma}
--     \left(\frac{\log|A|}{\eta T}+\frac{\eta\beta W^2}{2}
--     +\frac{1}{T}\sum_{i<T}\mathrm{err}_i\right).
--   $$
--
--   This isolates the deterministic optimization term from the prediction error later controlled by (25) and (26).
--
--   **Formalization Note** Strict positivity and differentiability are implicit in the assertion that every log action probability is smooth: Lean assigns a default value to the logarithm at zero and a totalized gradient at nondifferentiability. Nonnegative β is implicit in the usual definition of a smoothness constant. The finite minimum is represented by the existence of an index attaining at most the displayed bound.
-- source:
--   arXiv:1908.00261v5, Lemma 6.2, pp. 37–38, (23)–(24)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Lemma 6.2, pp. 37–38, the deterministic NPG regret lemma. -/
theorem npg_regret_lemma {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πtilde : S → A → ℝ) (hπtilde : IsPolicy πtilde)
    (pol : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (hpol : ∀ x, IsPolicy (pol x))
    (hpos : ∀ x s a, 0 < pol x s a)
    (β : ℝ) (hβ : 0 ≤ β)
    (hdiff : ∀ s a, Differentiable ℝ (fun z => Real.log (pol z s a)))
    (hsmooth : ∀ s a x y,
      ‖gradient (fun z => Real.log (pol z s a)) x -
        gradient (fun z => Real.log (pol z s a)) y‖ ≤ β * ‖x - y‖)
    (η W : ℝ) (hη : 0 < η)
    (T : ℕ) (hT : 0 < T)
    (θ w : ℕ → EuclideanSpace ℝ (Fin d))
    (hupdate : ∀ t < T, θ (t + 1) = θ t + η • w t)
    (hinit : ∀ s a, pol (θ 0) s a = 1 / (Fintype.card A : ℝ))
    (hw : ∀ t ≤ T, ‖w t‖ ≤ W) :
    ∃ t : ℕ, t < T ∧
      PolicyGradTheory.ProjGA.valueAt πtilde P r γ ρ - PolicyGradTheory.ProjGA.valueAt (pol (θ t)) P r γ ρ ≤
        (1 / (1 - γ)) *
          (Real.log (Fintype.card A : ℝ) / (η * T) + η * β * W ^ 2 / 2 +
            (1 / (T : ℝ)) * ∑ i ∈ Finset.range T,
              ∑ s : S, PolicyGradTheory.ProjGA.visitation πtilde P γ ρ s *
                ∑ a : A, πtilde s a *
                  (PolicyGradTheory.ProjGA.advantage (pol (θ i)) P r γ s a -
                    inner ℝ (w i) (gradient (fun z => Real.log (pol z s a)) (θ i)))) := by sorry

end PolicyGradTheory.QNPG
