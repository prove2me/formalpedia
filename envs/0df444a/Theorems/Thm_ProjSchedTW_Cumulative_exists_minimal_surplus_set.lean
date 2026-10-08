-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_exists_minimal_surplus_set
-- name    : ProjSchedTW.Cumulative.exists_minimal_surplus_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T00:00:46.704804+00:00
-- url     : https://prove2.me/theorems/5dc79f35-7804-41a3-b3a6-62ee75760e24
-- title:
--   Lemma 2.12.3 (a) — every k-surplus set contains the replenishments of a minimal k-surplus set
-- statement:
--   Consider a project with discrete cumulative resources as in §2.12.1, and assume Remark 2.12.2: $\underline R_k\le 0\le\overline R_k$ for every resource $k$. Let $k$ be a resource and $F$ a $k$-surplus set, i.e. a nonempty set of activities with $\sum_{i\in F}r_{ik}>\overline R_k$. Then there exists a minimal $k$-surplus set $F'$ with
--   $$
--   \emptyset\neq\{j\in F'\mid r_{jk}>0\}\subseteq\{j\in F\mid r_{jk}>0\}\quad\text{and}\quad\{j\in F'\mid r_{jk}<0\}\supseteq\{j\in F\mid r_{jk}<0\}.
--   $$
--
--   The lemma lets one pass from any inventory excess to a minimal surplus set that uses only replenishments that have already occurred and every depletion that has occurred; it is the first step of the sufficiency part of Theorem 2.12.4.
--
--   **Formalization Note** Minimality is the one-sided notion of p. 131 (`IsMinimalSurplusSet`), not inclusion-minimality. Assumption (2.12.1) is not needed and not assumed.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 132, Lemma 2.12.3 (a)

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- Lemma 2.12.3 (a). -/
theorem exists_minimal_surplus_set {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (k : K) (F : Finset (Fin (n + 2)))
    (hF : IsSurplusSet P k F) :
    ∃ F' : Finset (Fin (n + 2)), IsMinimalSurplusSet P k F' ∧
      (F'.filter (fun j => 0 < P.r j k)).Nonempty ∧
      F'.filter (fun j => 0 < P.r j k) ⊆ F.filter (fun j => 0 < P.r j k) ∧
      F.filter (fun j => P.r j k < 0) ⊆ F'.filter (fun j => P.r j k < 0) := by sorry

end ProjSchedTW.Cumulative
