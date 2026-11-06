-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_5_1
-- name    : PolytopeSchedPF.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:28.212198+00:00
-- url     : https://prove2.me/theorems/7da06ded-cff1-47fe-9373-864fd82588d4
-- title:
--   Lemma 5.1 — unique prices $\alpha^\pi$ with tight suffixes
-- statement:
--   Let $w>0$ and let $\pi$ be an order of $J$. There is a unique vector $\alpha^\pi\in\mathbb R^n_{\ge0}$ such that every suffix of $\pi$ is tight for $\alpha^\pi$:
--   $$
--   H_{\alpha^\pi}(S^\pi_b)=w(S^\pi_b)\qquad\text{for all }b\in[n+1].
--   $$
--   The prices $\alpha^\pi$ depend only on $\pi$, the weights and the polytope, not on $p$; Theorem 5.6 expresses $\mathrm{OPT}(p)$ as $\min_\pi\langle\alpha^\pi,p\rangle$.
--
--   Differences from the source:
--   - encoding: b ∈ [n+1], S^π_{n+1} = ∅ → 0-based b ≤ n, suffix π n = ∅; reason: positions of Fin n start at 0
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 5.1, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

/-- **Lemma 5.1** (Prices with tight suffixes; Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.1, p.26). For every order `π ∈ S_n`, there is
a unique vector `α^π ∈ ℝⁿ_{≥0}` such that every suffix of `π` is tight for `α^π`, that is,
`H_{α^π}(S^π_b) = w(S^π_b)` for all `b ∈ [n + 1]`.

**Formalization Note** Positions are 0-based (reading R14): the paper's `b ∈ [n+1]` is `b ≤ n` and
`S^π_{n+1} = suffix π n = ∅`. Uniqueness is among nonnegative vectors, as printed. -/
theorem lemma_5_1 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (π : Equiv.Perm (Fin n)) :
    ∃! α : Fin n → ℝ, (∀ j, 0 ≤ α j) ∧
      ∀ b : ℕ, b ≤ n → P.H α (suffix π b) = wsum w (suffix π b) := by sorry

end PolytopeSchedPF
