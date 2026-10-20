-- Prove2me | Theorems.Thm_ShapleyAttribution_UniqueUniform_proposition_1
-- name    : ShapleyAttribution.UniqueUniform.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:31.205979+00:00
-- url     : https://prove2.me/theorems/124a14a6-1d5a-4485-a645-f8445b61c6f9
-- title:
--   Proposition 1, p. 20 — Shapley value equals unique-uniform attribution
-- statement:
--   For a valid absorbing Markov attribution model $\mathcal M$ and a player $r=(s,a)$, let $\pi_r^{\mathrm{Shap}}$ be the Shapley value of the coalition conversion game. On a converting path $\mathcal P$, let $u(\mathcal P)$ count its distinct state-action pairs, and let $w_r(\mathcal P)=1/u(\mathcal P)$ if $r$ appears and zero otherwise. Then
--
--   $$\pi_r^{\mathrm{Shap}}=\mathbb E_{\mathcal P\sim\mathcal M}[w_r(\mathcal P)].$$
--
--   The identity replaces an exponential coalition sum with an expectation of a path-wise attribution weight. **Formalization Note** The expectation is a real sum over finite converting paths, so nonconverting paths contribute zero.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), p. 20, Proposition 1

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

namespace ShapleyAttribution.UniqueUniform

theorem proposition_1 {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (r : Fin m × Fin n) :
    M.shap r = M.pathExp (wUU r) := by sorry

end ShapleyAttribution.UniqueUniform
