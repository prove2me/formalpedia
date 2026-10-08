-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_lex_decrease
-- name    : SchrijverSFM.Alg.lex_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:50.508114+00:00
-- url     : https://prove2.me/theorems/0e8d4b3a-d5cb-4235-9f62-660a9f33986f
-- title:
--   Display (21), §5, pp. 352–353 — if d′ = d then (d′(t′), t′, s′, α′, β′) is lexicographically less than (d(t), t, s, α, β)
-- statement:
--   Let $S \to S'$ be one iteration of the algorithm with chosen elements $t, s$, and let $\alpha, \beta$ be the corresponding quantities of $S$: $\alpha = \max_i |(s,t]_{\prec_i}|$ and $\beta$ the number of $i$ with $|(s,t]_{\prec_i}| = \alpha$. Suppose the next state $S'$ is again in Case 2, with chosen elements $t', s'$ and quantities $\alpha', \beta'$ (computed in $S'$), and suppose $d'(v) = d(v)$ for all $v \in V$. Then
--   $$(d'(t'), t', s', \alpha', \beta') <_{\mathrm{lex}} (d(t), t, s, \alpha, \beta).$$
--
--   While the distance labels stay fixed, this tuple strictly decreases from iteration to iteration. Since it takes at most polynomially many values, $d$ must increase after a bounded number of iterations.
--
--   **Formalization Note** $t$, $s$ are compared in the numbering of $V$, distances in $\mathbb{N} \cup \{\infty\}$, and the order is lexicographic on the five-tuple. "The next iteration is again Case 2" is encoded by the hypotheses that $t'$ and $s'$ satisfy the choice rule of §4 in $S'$. No submodularity is needed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 352–353, displays (19) and (21)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem lex_decrease {n : ℕ} (f : Finset (Fin n) → ℝ)
    (S S' : State n) (t s : Fin n) (i : ℕ) (hstep : StepVia f S S' t s i)
    (t' s' : Fin n) (ht' : IsChosenT f S' t') (hs' : IsChosenS f S' t' s')
    (hd : ∀ v : Fin n, dist f S' v = dist f S v) :
    lexKey (dist f S' t') t' s' (alpha S' s' t') (beta S' s' t') <
      lexKey (dist f S t) t s (alpha S s t) (beta S s t) := by sorry
end SchrijverSFM.Alg
