-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_D_eq_lex_max
-- name    : VeinottSensitiveDP.Sensitive.D_eq_lex_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:52.048544+00:00
-- url     : https://prove2.me/theorems/4511a389-948c-4f46-8841-1346aee06db2
-- title:
--   §4, p. 1646 — D_n^± = {f : Y_n^±(f) ⪰ Y_n^±(g) for all g ∈ F}, n = −1, 0, ⋯
-- statement:
--   In the model of §4, for $n=-1,0,1,\dots$ (and, for the sign $-$, in the transient case),
--   $$D_n^\pm=\{f\in F:\ Y_n^\pm(f)\succeq Y_n^\pm(g)\text{ for all }g\in F\},$$
--   where $\succeq$ is the lexicographic order applied row by row to the $S\times(n+2)$ matrices of Laurent coefficients $(y_{-1}^\pm,\dots,y_n^\pm)$.
--
--   So $n^\pm$ discount optimality of a stationary policy against all policies reduces to a finite lexicographic comparison among stationary policies.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. $D_n^\pm$ is defined through the $\liminf$ criterion (27) against all policies; the right-hand side involves only stationary policies. The sentence of the paper continues with the analogous statement for $D_\infty^\pm$, which is not included.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4 ("Since D_n^± is nonempty, it is immediate from (29) that D_n^± = {f: f ε F, Y_n^±(f) ⪰ Y_n^±(g) for all g ε F} for n = −1, 0, ⋯")

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Characterization of `D_n^±`: for `n = −1, 0, ⋯`,
`D_n^± = {f : f ε F, Y_n^±(f) ⪰ Y_n^±(g) for all g ε F}`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4 ("Since D_n^± is nonempty, it is immediate from (29) that D_n^± = …").

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; the `−` case assumes the transient case, where alone
`n⁻` discount optimality is defined. `D_n^±` is defined through (27) by comparison with **all**
policies; the right side compares the Laurent coefficients with those of the stationary policies
only. `Y_n^±(f) ⪰ Y_n^±(g)` is `LexNonneg n (Y_n^±(f) − Y_n^±(g))`, row by row over the states,
on the columns `−1, …, n`. The continuation of the sentence about `D_∞^±` (infinite `Y^±`) is not
included. -/
theorem D_eq_lex_max {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) (n : ℤ) (hn : -1 ≤ n) :
    M.D σ n = {f | ∀ g : DecisionRule A, LexNonneg n (M.Y σ f n - M.Y σ g n)} := by sorry

end VeinottSensitiveDP.Sensitive
