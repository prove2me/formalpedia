-- Prove2me | Theorems.Thm_ShapleyAttribution_UniqueUniform_step_1_paths
-- name    : ShapleyAttribution.UniqueUniform.step_1_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:29.31602+00:00
-- url     : https://prove2.me/theorems/a7763a26-a5a1-45c5-87bb-3cedaaf80385
-- title:
--   Proof of Proposition 1, Step 1, p. 21 — coalition value as a converting-path expectation
-- statement:
--   Let $\mathcal M$ be a valid absorbing Markov attribution model, $X\subseteq\mathbb P$ a coalition, and $\mathcal X(\mathcal P)$ the distinct players occurring in a path. The coalition conversion value is
--
--   $$v(X)=\mathbb E_{\mathcal P\sim\mathcal M}\!\left[\mathbf1\{\mathcal P\text{ converts}\}\,\mathbf1\{\mathcal X(\mathcal P)\subseteq X\}\right].$$
--
--   This expresses coalition value using paths of the original model and the condition that every player on the path belongs to the coalition. **Formalization Note** The real `tsum` ranges over finite converting paths; its probability is zero on an empty path.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), p. 21, proof of Proposition 1, Step 1

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

namespace ShapleyAttribution.UniqueUniform

theorem step_1_paths {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (X : Finset (Fin m × Fin n)) :
    M.val X ∅ = M.pathExp (fun path => if path.toFinset ⊆ X then 1 else 0) := by sorry

end ShapleyAttribution.UniqueUniform
