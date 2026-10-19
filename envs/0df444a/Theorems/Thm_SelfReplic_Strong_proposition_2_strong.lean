-- Prove2me | Theorems.Thm_SelfReplic_Strong_proposition_2_strong
-- name    : SelfReplic.Strong.proposition_2_strong
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:56.95588+00:00
-- url     : https://prove2.me/theorems/57015884-2eab-4007-bff7-5c8d751a67b0
-- title:
--   Proposition 2 (first half), p. 9 — under Strong Replicability an optimal policy keeps inventory positive until T
-- statement:
--   Consider the base model under the standing assumptions, and assume Strong Replicability
--   $$(r-\rho)\pi>cr+h.$$
--   Then every optimal trajectory keeps the inventory positive before the end of the life cycle:
--   $$I(t)>0\qquad\text{for all }0\le t<T.$$
--   This holds for every horizon $T>0$.
--
--   This is the first half of the paper's Proposition 2: under Strong Replicability the product life cycle lasts until $T$, however large $T$ is. It is why the optimal policies of Theorem 1 never stock out before $T$.
--
--   **Formalization Note** The second half of Proposition 2, about the Weak Replicability regime $(r-\rho)\pi<cr+h$, is not formalized. It is false when $I_L\ge m$, since total sales never exceed $m$, and Theorem 1 does not use it. "Regardless of how large $T$ is" is the universal quantification over the horizon $T$ in the parameters.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 9, Proposition 2 (first half, up to the semicolon; proof p. 36)

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

/-- Proposition 2 (first half), p. 9: under Strong Replicability `(r − ρ)π > cr + h`, every
optimal trajectory keeps the inventory positive before `T`, whatever the horizon `T`. -/
theorem proposition_2_strong (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (x : Traj) (hx : IsOptimal P x) :
    ∀ t ∈ Set.Ico 0 P.T, 0 < x.I t := by sorry

end SelfReplic.Strong
