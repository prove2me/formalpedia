-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_5_4
-- name    : PolytopeSchedPF.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:59.656069+00:00
-- url     : https://prove2.me/theorems/54c8bce5-abe2-4f05-80d0-f244fcd0146d
-- title:
--   Lemma 5.4 — tight suffixes propagate to $H_\alpha(U)\ge w(U)$ for all $U$
-- statement:
--   Consider a support-submodular PSP instance with weights $w>0$, an order $\pi$, and $\alpha\in\mathbb R^n_{\ge0}$ such that every suffix of $\pi$ is tight for $\alpha$, $H_\alpha(S^\pi_b)=w(S^\pi_b)$. Then
--   $$
--   H_\alpha(U)\ge w(U)\qquad\text{for all }U\subseteq J .
--   $$
--   This is the only place where the analysis uses support submodularity.
--
--   Differences from the source:
--   - encoding: every suffix S^π_b, b ∈ [n+1] → suffix π b for 0-based b ≤ n; reason: positions of Fin n start at 0
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 5.4, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders
import Definitions.Def_PolytopeSchedPF_IsSupportSubmodular

namespace PolytopeSchedPF

/-- **Lemma 5.4** (Suffix-to-all-sets propagation; Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.2, p.27). Consider a
support-submodular PSP instance, and let `π ∈ S_n` and `α ∈ ℝⁿ_{≥0}` such that every suffix of
`π` is tight for `α`. Then `H_α(U) ≥ w(U)` for all `U ⊆ J`.

**Formalization Note** "Every suffix" is `suffix π b` for `b ≤ n` (0-based, reading R14), and a set
`S` is tight for `α` if `H_α(S) = w(S)` (p.25). -/
theorem lemma_5_4 {n D : ℕ} (P : RatePolytope n D) (hP : IsSupportSubmodular P)
    (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (π : Equiv.Perm (Fin n)) (α : Fin n → ℝ)
    (hα : ∀ j, 0 ≤ α j) (htight : ∀ b : ℕ, b ≤ n → P.H α (suffix π b) = wsum w (suffix π b)) :
    ∀ U : Finset (Fin n), wsum w U ≤ P.H α U := by sorry

end PolytopeSchedPF
