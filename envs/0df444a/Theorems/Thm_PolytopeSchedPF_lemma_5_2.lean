-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_5_2
-- name    : PolytopeSchedPF.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:42.538559+00:00
-- url     : https://prove2.me/theorems/9aeb1c9a-6c00-4bc6-a92c-da5b8d1a2ea3
-- title:
--   Lemma 5.2 — fixed-order lower bound
-- statement:
--   Let $w>0$, let $\pi$ be an order and $\alpha\in\mathbb R^n_{\ge0}$ with $H_\alpha(S^\pi_b)\le w(S^\pi_b)$ for all $b\in[n]$. Then for every $p\in\mathbb R^n_{\ge0}$, every feasible schedule for $p$ (release dates $0$) that completes the jobs in the order $\pi$ has
--   $$
--   \sum_jw_jC_j\ \ge\ \langle\alpha,p\rangle .
--   $$
--   In particular, $\langle\alpha^\pi,p\rangle\le\mathrm{OPT}_\pi(p)$, where $\alpha^\pi$ is the price vector of Lemma 5.1.
--
--   This is the lower half of Theorem 5.6: each fixed completion order has a linear lower bound in $p$.
--
--   Differences from the source:
--   - encoding: b ∈ [n] → 0-based b < n; reason: positions of Fin n start at 0
--   - encoding: α^π of Lemma 5.1 → any nonnegative vector for which every suffix of π is tight; reason: Lemma 5.1 makes this vector unique
--   - encoding: OPT_π(p) with inf ∅ := ∞ → optOrder in EReal; reason: the paper's ∞ is representable only in an extended type
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 5.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

/-- **Lemma 5.2** (Fixed-order lower bound; Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.1, p.26). Let `π ∈ S_n` and `α ∈ ℝⁿ_{≥0}` such
that `H_α(S^π_b) ≤ w(S^π_b)` for all `b ∈ [n]`. Then, for every `p ∈ ℝⁿ_{≥0}`, every feasible
schedule for `p` that completes the jobs in the order `π` has weighted completion time at least
`⟨α, p⟩`. In particular, `⟨α^π, p⟩ ≤ OPT_π(p)`.

**Formalization Note** Release dates are `0` (§5); schedules are not assumed normalized. Positions
are 0-based (reading R14): `b ∈ [n]` is `b < n`. In the in-particular clause `α^π` is any
nonnegative vector for which every suffix of `π` is tight (unique by Lemma 5.1), and `OPT_π` is
`optOrder` in `EReal`. -/
theorem lemma_5_2 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (π : Equiv.Perm (Fin n)) :
    (∀ α : Fin n → ℝ, (∀ j, 0 ≤ α j) →
      (∀ b : ℕ, b < n → P.H α (suffix π b) ≤ wsum w (suffix π b)) →
      ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) →
        ∀ y, IsFeasible P p 0 y → CompletesInOrder p 0 y π →
          dot α p ≤ weightedCompletion w p 0 y) ∧
    (∀ απ : Fin n → ℝ, (∀ j, 0 ≤ απ j) →
      (∀ b : ℕ, b ≤ n → P.H απ (suffix π b) = wsum w (suffix π b)) →
      ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) →
        ((dot απ p : ℝ) : EReal) ≤ optOrder P w p π) := by sorry

end PolytopeSchedPF
