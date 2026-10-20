-- Prove2me | Theorems.Thm_ShapleyAttribution_UniqueUniform_theorem_2
-- name    : ShapleyAttribution.UniqueUniform.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:25.922976+00:00
-- url     : https://prove2.me/theorems/5d9b6e6e-9843-45d8-9638-97ece5f44610
-- title:
--   Theorem 2, p. 22 — CASV equals unique-uniform minus its counterfactual
-- statement:
--   Let $\mathcal M$ be a valid absorbing Markov attribution model, $r=(s,a)$ a state-action player, and $\mathcal M_r$ its counterfactual chain, also absorbing. On a converting path $\mathcal P$, let $w_r(\mathcal P)=1/u(\mathcal P)$ if $r$ occurs, where $u$ counts distinct state-action pairs, and zero otherwise. The counterfactual adjusted Shapley value satisfies
--
--   $$\psi_r^{\mathrm{Shap}}=\mathbb E_{\mathcal P\sim\mathcal M}[w_r(\mathcal P)]-\mathbb E_{\mathcal P\sim\mathcal M_r}[w_r(\mathcal P)].$$
--
--   This characterizes the coalition-based CASV by two converting-path expectations, one under the original network and one under the counterfactual network.
--
--   **Formalization Note** The paper's Assumption 1 is imposed separately on $\mathcal M_r$; absorption of $\mathcal M$ does not imply it. The counterfactual keeps $r$ as a player at its original frequency and substitutes the no-ad transition row, as required by the displayed counterfactual marginal in Appendix B, p. 46.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), p. 22, Theorem 2; p. 46, Appendix B, counterfactual marginal

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

namespace ShapleyAttribution.UniqueUniform

theorem theorem_2 {m n : ℕ} (M : Model m n) (hM : M.Valid)
    (hA : M.Absorbing) (r : Fin m × Fin n)
    (hAcf : (M.cfModel r).Absorbing) :
    M.casv r = M.pathExp (wUU r) - (M.cfModel r).pathExp (wUU r) := by sorry

end ShapleyAttribution.UniqueUniform
