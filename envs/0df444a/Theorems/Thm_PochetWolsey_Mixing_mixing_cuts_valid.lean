-- Prove2me | Theorems.Thm_PochetWolsey_Mixing_mixing_cuts_valid
-- name    : PochetWolsey.Mixing.mixing_cuts_valid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:14.050144+00:00
-- url     : https://prove2.me/theorems/24967769-6985-474f-9801-4bf5a489e5d9
-- title:
--   Proposition 8.4 — validity of both mixing inequalities
-- statement:
--   Let $b\in\mathbb R^K$ and let $T$ be a nonempty coordinate subset with an enumeration $i_1,\ldots,i_q$ such that $f_{i_1}\le\cdots\le f_{i_q}$, where $f_k=b_k-\lfloor b_k\rfloor$ and $f_{i_0}=0$. Every $(s,y)\in X^{MIX}_K(b)$ satisfies both inequalities
--   $$
--   s\ge\sum_{\tau=1}^q(f_{i_\tau}-f_{i_{\tau-1}})(\lfloor b_{i_\tau}\rfloor+1-y_{i_\tau}),
--   $$
--   $$
--   s\ge\sum_{\tau=1}^q(f_{i_\tau}-f_{i_{\tau-1}})(\lfloor b_{i_\tau}\rfloor+1-y_{i_\tau})+(1-f_{i_q})(\lfloor b_{i_1}\rfloor-y_{i_1}).
--   $$
--   These are companion validity results on the same mixing model.
--
--   **Formalization Note** An injective map from `Fin (t+1)` enumerates the nonempty subset, with weak monotonicity preserving ties. Nonemptiness is implicit in the printed use of first and last elements. The bounds $0\le f_k<1$ follow from the definition of fractional part and are not additional assumptions. The singleton case is included.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 242 (PDF 256), Proposition 8.4, Eqs. (8.7)–(8.8)

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Cuts

namespace PochetWolsey.Mixing

theorem mixing_cuts_valid {K t : ℕ} (b : Fin K → ℝ)
    (i : Fin (t + 1) → Fin K) (hi : Function.Injective i)
    (horder : Monotone (fun j => frac (b (i j)))) :
    ∀ p ∈ mixingSet b, cutRhs b i p.2 ≤ p.1 ∧ wrapCutRhs b i p.2 ≤ p.1 := by sorry

end PochetWolsey.Mixing
