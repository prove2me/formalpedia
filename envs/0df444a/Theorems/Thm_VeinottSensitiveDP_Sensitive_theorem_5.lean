-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_theorem_5
-- name    : VeinottSensitiveDP.Sensitive.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:17.47898+00:00
-- url     : https://prove2.me/theorems/114b741b-03c4-40d0-8f74-07e25562dceb
-- title:
--   Theorem 5 — if Ψ_{n−1}^±(g, f) = 0 then Y_{n−2}^±(g) = Y_{n−2}^±(f); if also g ∈ G_n^±(f) ∩ G_{n+1}^±(f), then Y_n^±(g) ≻ Y_n^±(f)
-- statement:
--   In the model of §4 (for the sign $-$, in the transient case), let $f,g\in F$ and $n\in\{-1,0,\dots,S\}$. If $\Psi_{n-1}^\pm(g,f)=0$, then
--   $$Y_{n-2}^\pm(g)=Y_{n-2}^\pm(f);$$
--   if moreover $g\in G_n^\pm(f)\cap G_{n+1}^\pm(f)$, then
--   $$Y_n^\pm(g)\succ Y_n^\pm(f).$$
--
--   The theorem says that a suitably chosen improvement of order $n$ strictly increases the Laurent coefficients lexicographically, which is what makes the policy improvement method for $n^\pm$ discount optimal policies terminate.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. $S$ is the number of states. $\succ$ is lexicographic positivity of the difference on the columns $-1,\dots,n$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1649, §4, Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Theorem 5: if `f, g ε F` and `Ψ_{n−1}^±(g, f) = 0`, then `Y_{n−2}^±(g) = Y_{n−2}^±(f)`; if also
`g ε G_n^±(f) ∩ G_{n+1}^±(f)`, then `Y_n^±(g) ≻ Y_n^±(f)`, for `n = −1, 0, ⋯, S`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1649, §4, Theorem 5.

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; the `−` case assumes the transient case (the paper's proof
"recall[s] P*(g) is presumed to vanish when ± is −"). `S = Fintype.card St`. `Y_n^±(g) ≻ Y_n^±(f)`
is `LexPos n (Y_n^±(g) − Y_n^±(f))`. `Ψ_{n−1}^±(g, f) = 0` is equality of the whole matrix
(it holds trivially for `n − 1 < −1`). -/
theorem theorem_5 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) (f g : DecisionRule A)
    (n : ℤ) (hn1 : -1 ≤ n) (hn2 : n ≤ (Fintype.card St : ℤ)) (hΨ : M.Ψ σ g f (n - 1) = 0) :
    M.Y σ g (n - 2) = M.Y σ f (n - 2) ∧
      (g ∈ M.G σ n f ∩ M.G σ (n + 1) f → LexPos n (M.Y σ g n - M.Y σ f n)) := by sorry

end VeinottSensitiveDP.Sensitive
