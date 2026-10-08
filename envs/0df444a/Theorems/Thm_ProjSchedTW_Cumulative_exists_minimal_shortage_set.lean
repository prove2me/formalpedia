-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_exists_minimal_shortage_set
-- name    : ProjSchedTW.Cumulative.exists_minimal_shortage_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T00:01:50.015347+00:00
-- url     : https://prove2.me/theorems/f35e7e5b-e30b-4e67-8b6e-bbc055c8c94a
-- title:
--   Lemma 2.12.3 (b) — every k-shortage set contains the depletions of a minimal k-shortage set
-- statement:
--   Consider a project with discrete cumulative resources as in §2.12.1, and assume Remark 2.12.2: $\underline R_k\le 0\le\overline R_k$ for every resource $k$. Let $k$ be a resource and $F$ a $k$-shortage set, i.e. a nonempty set of activities with $\sum_{i\in F}r_{ik}<\underline R_k$. Then there exists a minimal $k$-shortage set $F'$ with
--   $$
--   \emptyset\neq\{j\in F'\mid r_{jk}<0\}\subseteq\{j\in F\mid r_{jk}<0\}\quad\text{and}\quad\{j\in F'\mid r_{jk}>0\}\supseteq\{j\in F\mid r_{jk}>0\}.
--   $$
--
--   This is the shortage counterpart of Lemma 2.12.3 (a) and is used in the shortage half of Theorem 2.12.4.
--
--   **Formalization Note** Minimality is the one-sided notion of p. 131 (`IsMinimalShortageSet`). Assumption (2.12.1) is not needed and not assumed.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 132, Lemma 2.12.3 (b)

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- Lemma 2.12.3 (b). -/
theorem exists_minimal_shortage_set {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (k : K) (F : Finset (Fin (n + 2)))
    (hF : IsShortageSet P k F) :
    ∃ F' : Finset (Fin (n + 2)), IsMinimalShortageSet P k F' ∧
      (F'.filter (fun j => P.r j k < 0)).Nonempty ∧
      F'.filter (fun j => P.r j k < 0) ⊆ F.filter (fun j => P.r j k < 0) ∧
      F.filter (fun j => 0 < P.r j k) ⊆ F'.filter (fun j => 0 < P.r j k) := by sorry

end ProjSchedTW.Cumulative
