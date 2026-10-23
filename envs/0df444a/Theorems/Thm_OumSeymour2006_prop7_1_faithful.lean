-- Prove2me | Theorems.Thm_OumSeymour2006_prop7_1_faithful
-- name    : OumSeymour2006.prop7_1_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:27:42.973949+00:00
-- url     : https://prove2.me/theorems/97a08b6b-8e26-4f57-86f2-406da87a1172
-- title:
--   Proposition 7.1 — $\lambda_B$ is an interpolation of the matroid connectivity function
-- statement:
--   Let $M$ be a matroid on a finite ground set $E$ with rank function $r$, and let
--
--   $$\lambda(X) = r(X) + r(E \setminus X) - r(E) + 1 \qquad (X \subseteq E)$$
--
--   be its connectivity function. Let $B$ be a base of $M$. Then the function on disjoint pairs
--
--   $$\lambda_B(X, Y) = r\bigl(X \cup (B \setminus Y)\bigr) + r\bigl(Y \cup (B \setminus X)\bigr) - |B \setminus X| - |B \setminus Y| + 1$$
--
--   is an interpolation of $\lambda$: $\lambda_B(X, E \setminus X) = \lambda(X)$, $\lambda_B$ is monotone on disjoint pairs, $\lambda_B$ is submodular on disjoint pairs, and $\lambda_B(\emptyset, \emptyset) = \lambda(\emptyset)$.
--
--   This is Proposition 7.1 of Oum and Seymour (attributed to J. Geelen). It is the key step behind Theorem 1.2: using $\lambda_B$ instead of $\lambda_{\min}$ lets the general branch-width algorithm run on matroids with matroid intersection in place of submodular function minimization.
--
--   **Formalization Note** The matroid is given by its rank function satisfying the rank axioms (i)–(iii) of p. 517 on the whole ground set. A base is encoded as an independent set ($r(B) = |B|$) of full rank ($r(B) = r(E)$), which is equivalent to being a maximal independent set in a matroid. Interpolation follows the existing platform definition, whose axioms are imposed on disjoint pairs only.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, doi:10.1016/j.jctb.2005.10.006, p. 525, Proposition 7.1

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

open ApproxCliqueWidth.Certificate

theorem OumSeymour2006.prop7_1_faithful {V : Type*} [Fintype V] [DecidableEq V]
    (r : Finset V → ℤ) (hr : IsMatroidRankOn Finset.univ r)
    (B : Finset V) (hBindep : r B = (B.card : ℤ)) (hBspan : r B = r Finset.univ) :
    IsInterpolation (fun X => r X + r Xᶜ - r Finset.univ + 1)
      (fun X Y => r (X ∪ (B \ Y)) + r (Y ∪ (B \ X))
        - ((B \ X).card : ℤ) - ((B \ Y).card : ℤ) + 1) := by sorry
