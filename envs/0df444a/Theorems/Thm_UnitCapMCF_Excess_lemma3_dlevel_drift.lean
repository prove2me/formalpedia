-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma3_dlevel_drift
-- name    : UnitCapMCF.Excess.lemma3_dlevel_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:39.424658+00:00
-- url     : https://prove2.me/theorems/faccc9ba-6cb9-441d-ab24-5b31badff39e
-- title:
--   Lemma 3, p. 410 — level drift along an arc of E⁺
-- statement:
--   Let $f'$ be $2\varepsilon$-optimal at entry prices $p'$, and let $f$ be $\varepsilon$-optimal at current prices $p$, where $\varepsilon>0$. Write $E^+=\{(v,w)\in E:f'(v,w)>f(v,w)\}$ and $d(x)=(p(x)-p'(x))/\varepsilon$. For every $(v,w)\in E^+$,
--
--   $$d(v)\le d(w)+3.$$
--
--   The level drift bound is the path constraint used to turn the level bands in Lemma 5 into excess–deficit cuts.
--
--   **Formalization Note** Both optimality predicates include the pseudoflow constraints. No circulation, unit-capacity or integrality assumption is needed for this lemma.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, Lemma 3; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, Lemma 3, p. 410. -/
theorem lemma3_dlevel_drift {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (ε : ℝ) (hε : 0 < ε)
    (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (v w : V) (hvw : (v, w) ∈ Eplus N f' f) :
    dlevel ε p' p v ≤ dlevel ε p' p w + 3 := by sorry

end UnitCapMCF.Excess
