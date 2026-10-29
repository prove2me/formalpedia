-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_krylov_membership
-- name    : PutermanMDP.Sensitive.krylov_membership
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:24.843694+00:00
-- url     : https://prove2.me/theorems/fecb4053-5eae-48b6-a79b-1310729489e3
-- title:
--   Lemma 10.3.3 — finite Krylov membership criterion
-- statement:
--   Let $H$ be a real $m\times m$ matrix of rank $p$, let $U\subseteq\mathbb R^m$ have dimension $q$, and let $x\in\mathbb R^m$. The printed statement asserts
--   $$[H^kx\in U\text{ for }k=1,\ldots,\min(p,q)]\ \Longrightarrow\ [H^kx\in U\text{ for all }k\ge1].$$
--   This is the linear-algebra statement used by the chapter's finite-determination argument. It is retained as printed; FINDINGS F1 gives a counterexample and a disproof is expected.
--
--   **Formalization Note** Rank and dimension are computed from $H$ and $U$, respectively; no invariance assumption is added.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 517 (PDF 533), Lemma 10.3.3; https://doi.org/10.1002/9780470316887

import Mathlib

namespace PutermanMDP.Sensitive

/-- Printed Lemma 10.3.3, retained faithfully; FINDINGS F1 gives a counterexample. -/
theorem krylov_membership (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ)
    (U : Submodule ℝ (Fin m → ℝ)) (x : Fin m → ℝ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ min H.rank (Module.finrank ℝ U) →
      (H ^ k).mulVec x ∈ U) :
    ∀ k : ℕ, 1 ≤ k → (H ^ k).mulVec x ∈ U := by sorry

end PutermanMDP.Sensitive
