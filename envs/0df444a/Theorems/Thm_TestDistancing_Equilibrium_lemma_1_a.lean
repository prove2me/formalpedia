-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_lemma_1_a
-- name    : TestDistancing.Equilibrium.lemma_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:05.163811+00:00
-- url     : https://prove2.me/theorems/6b36b677-be50-4190-96e1-a52127118dc2
-- title:
--   Lemma 1(a) — infection increases with social activity
-- statement:
--   For any agent $i$, two activity profiles $x,\hat x\in[0,1]^n$ with $x_j\le\hat x_j$ for every $j$, and a testing policy $(\alpha_L,\alpha_H)\in[0,1]^2$,
--
--   $$P_i^{\mathrm{inf}}(x,\alpha_L,\alpha_H)\le P_i^{\mathrm{inf}}(\hat x,\alpha_L,\alpha_H).$$
--
--   This is the model's activity monotonicity result and feeds the equilibrium comparison.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 9 (PDF 11), Lemma 1(a), (2)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem lemma_1_a (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x y : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (hxy : ∀ j, x j ≤ y j) (i : Fin n) :
    Pinf P x α i ≤ Pinf P y α i := by sorry

end TestDistancing.Equilibrium
