-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_performance_difference
-- name    : PolicyGradTheory.QNPG.performance_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:29.040537+00:00
-- url     : https://prove2.me/theorems/bba0de43-9477-4c1e-9113-75c03b7d1c3a
-- title:
--   Lemma 3.2, p. 12 — performance difference identity
-- statement:
--   Let π and π′ be stationary policies in a finite discounted MDP, and start from a state s₀. The change in unnormalized discounted value is the discounted visitation average, under π, of π′'s advantage:
--
--   $$
--   V^\pi(s_0)-V^{\pi'}(s_0)
--     =\frac{1}{1-\gamma}\mathbb E_{s\sim d^\pi_{s_0}}
--       \mathbb E_{a\sim\pi(\cdot\mid s)}[A^{\pi'}(s,a)].
--   $$
--
--   This identity converts comparisons between policies into expectations of advantages and is used in the regret analysis.
-- source:
--   arXiv:1908.00261v5, Lemma 3.2, p. 12

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Lemma 3.2, p. 12, in the paper's unnormalized value convention. -/
theorem performance_difference {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      (1 / (1 - γ)) *
        ∑ s : S, PolicyGradTheory.ProjGA.visitation π P γ (fun x => if x = s₀ then 1 else 0) s *
          ∑ a : A, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by sorry

end PolicyGradTheory.QNPG
