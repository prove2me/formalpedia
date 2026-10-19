-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_proposition_1_convex
-- name    : PrepoLocal.Threshold.proposition_1_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:10.978046+00:00
-- url     : https://prove2.me/theorems/19b3388a-35b5-40de-ba9d-7a18c12de97d
-- title:
--   Proposition 1, p. 8 (first clause) — the expected cycle cost C(x) is convex
-- statement:
--   In the single-cycle prepo model (standing assumptions as in the model definition), the expected cycle cost
--   $$
--   C(x)=\mathbb E\bigl[iTx+\alpha\min\{D,Q,\hat b(x,R,T)/\alpha\}+\min\{x,S(x)\}+v(S(x)-x)^+\bigr],\qquad \hat b(x,R,T)=b+\gamma T+R-x,
--   $$
--   is a convex function of the prepo level $x$.
--
--   Convexity of $C$ is the structural property behind the paper's characterization of the optimal prepo stock as $\min\{(x^o)^+,b\}$, with $x^o$ the root of the marginal cost.
--
--   **Formalization Note** Only the first clause of Proposition 1 is formalized. The second clause, $x^*=\min\{(x^o)^+,b\}$ with $x^o=m^{-1}(0)$, is expressed through the derivatives (2)–(3), which need the densities $f_{DQR}$, $f_T$, and presumes a root of $m$; it is not part of this statement. Convexity is stated on the whole real line, which contains the paper's domain.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 8, Proposition 1 (first clause)

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- Proposition 1, p. 8 (first clause): the expected cycle cost `C(x)` is convex. -/
theorem proposition_1_convex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ) :
    ConvexOn ℝ Set.univ (C P μ E) := by sorry

end PrepoLocal.Threshold
