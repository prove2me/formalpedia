-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_3
-- name    : WaitTimePricing.Existence.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:47.699182+00:00
-- url     : https://prove2.me/theorems/1b4b2d80-0a05-4882-b73f-599225296d30
-- title:
--   Proposition 3 — (V1) $\mathbf v(p)\le U'(0)\mathtt t(p)$ and (V2) for both objectives
-- statement:
--   For either objective of Lemma 1 (revenue, $\mathbf v(p)=p\,\mathtt t(p)$; social welfare, $\mathbf v(p)=U(\mathtt t(p))$):
--
--   1. (V1) $\mathbf v(p)\le U'(0)\,\mathtt t(p)$ for all $p\in[0,U'(0)]$;
--   2. (V2) $\mathbf v(U'(0))=0$, and there is $p\in[0,U'(0))$ with $\mathbf v(p)>0$.
--
--   (V1) bounds the value a customer can generate and is used in the existence construction; (V2) says that the highest price brings no value while some lower price does.
--
--   **Formalization Note** (V1) is printed "for all $p\ge0$", but $\mathtt t(p)$ is defined only on $[0,U'(0)]$ (5), and the paper's proof establishes it there; it is stated on $[0,U'(0)]$. The printed "$\mathbf v(p)=0$ $\forall p=U'(0)$" is read as $\mathbf v(U'(0))=0$.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, Proposition 3, (V1), (V2)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, Proposition 3, (V1)–(V2).

For either objective of Lemma 1 (revenue `v(p) = p·t(p)`, or welfare `v(p) = U(t(p))`):
(V1) `v(p) ≤ U′(0) t(p)`; (V2) `v(U′(0)) = 0`, and `v(p) > 0` for some `p ∈ [0, U′(0))`.

**Formalization Note.** (V1) is printed for all `p ≥ 0`, but `t(p)` is defined only on
`[0, U′(0)]` (5) and the proof (p. 32) establishes it there; it is stated on `[0, U′(0)]`. The
printed "`v(p) = 0 ∀p = U′(0)`" means `v(U′(0)) = 0`. -/
theorem proposition_3 (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ p ∈ Icc 0 (deriv M.U 0), v M obj p ≤ deriv M.U 0 * tOf M p) ∧
    v M obj (deriv M.U 0) = 0 ∧
    ∃ p ∈ Ico 0 (deriv M.U 0), 0 < v M obj p := by sorry

end WaitTimePricing.Existence
