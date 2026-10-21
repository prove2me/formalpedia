-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_lemma_1_b
-- name    : TestDistancing.Equilibrium.lemma_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:08.494198+00:00
-- url     : https://prove2.me/theorems/4ed820dd-65bc-47f8-bca4-03ececf96cac
-- title:
--   Lemma 1(b) — concavity in own activity
-- statement:
--   Fix an agent $i$, the other agents' activity profile $x_{-i}\in[0,1]^{n-1}$, and a testing policy $(\alpha_L,\alpha_H)\in[0,1]^2$. Then
--
--   $$t\longmapsto P_i^{\mathrm{inf}}((t,x_{-i}),\alpha_L,\alpha_H)$$
--
--   is concave on $[0,1]$. This makes the agent's utility convex in her own activity, the basis for the endpoint best-response statement.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 9 (PDF 11), Lemma 1(b)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem lemma_1_b (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t => Pinf P (Function.update x i t) α i) := by sorry

end TestDistancing.Equilibrium
