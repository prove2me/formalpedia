-- Prove2me | Theorems.Thm_ShapleyAttribution_UniqueUniform_eq_6
-- name    : ShapleyAttribution.UniqueUniform.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:33.748204+00:00
-- url     : https://prove2.me/theorems/e3c9873f-1c8c-492a-9a21-2b94853d1530
-- title:
--   (6), p. 16 — CASV is a difference of Shapley values
-- statement:
--   Let $\mathcal M$ be the Markov attribution model and $r=(s,a)$ a state-action player. Let $\mathcal M_r$ retain player $r$ but replace its transition row by the no-ad row. Then
--
--   $$\psi_r^{\mathrm{Shap}}(\mathcal M)=\pi_r^{\mathrm{Shap}}(\mathcal M)-\pi_r^{\mathrm{Shap}}(\mathcal M_r).$$
--
--   This identifies CASV as a difference of two ordinary coalition-game Shapley values. **Formalization Note** The identity is algebraic and requires no stochastic or absorption hypotheses.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), p. 16, display (6)

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

namespace ShapleyAttribution.UniqueUniform

theorem eq_6 {m n : ℕ} (M : Model m n) (r : Fin m × Fin n) :
    M.casv r = M.shap r - (M.cfModel r).shap r := by sorry

end ShapleyAttribution.UniqueUniform
