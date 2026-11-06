-- Prove2me | Theorems.Thm_UninformedMG_vdagger_rounding
-- name    : UninformedMG.vdagger_rounding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:20.501447+00:00
-- url     : https://prove2.me/theorems/038a7748-03ed-42dc-bd00-4f46a9dcac8e
-- title:
--   p.25 — the rounded empirical value $v^\dagger$ lies in $\mathcal V$, approximates $V^{\mathrm{emp}}/H$, and has nonpositive residuals under $\mu^{\mathrm{emp}}$
-- statement:
--   Let $H\ge2$, $K\ge1$ and let $\nu^1,\dots,\nu^K$ be opponent Markov policies. Then some learner Markov policy $\mu^{\mathrm{emp}}$ attains the minimum in Eq. (1) at every $(h,s)$. For every such $\mu^{\mathrm{emp}}$, the rounded empirical value $v^\dagger$ satisfies:
--
--   1. $v^\dagger\in\mathcal V$, the grid of Eq. (19);
--   2. $0\le v^\dagger_h(s)-V^{\mathrm{emp}}_h(s)/H\le(H-h+1)/(HK)$ for every $h\ge2$ and $s\in S_h$;
--   3. $\sum_a\mu^{\mathrm{emp}}_h(a\mid s)Y^k_{h,s,v^\dagger,a}\le v^\dagger_h(s)$ for every episode $k$, $h\ge2$ and $s\in S_h$;
--   4. $\sum_a\mu^{\mathrm{emp}}_1(a\mid s)Y^k_{1,s,v^\dagger,a}\le V^{\mathrm{emp}}_1(s)/H+(H-1)/(HK)$ for every $k$ and $s\in S_1$.
--
--   Here $Y^k$ is computed from $\nu^k$ and $v^\dagger$. This is the deterministic step that brings the per-state, data-dependent benchmark $V^{\mathrm{emp}}$ into the fixed grid.
--
--   Differences from the source:
--   - generalization: "let μ^emp attain the minimum in Eq. (1)" → also asserts that such a μ^emp exists; reason: the proof takes existence for granted (a continuous function on a compact simplex); dropping the clause gives the printed claims
--   - encoding: the realized opponent-policy sequence → arbitrary opponent Markov policies ν^1, …, ν^K; reason: the claims are deterministic; the realized sequence is one instance
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), proof of Theorem 2.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_potQ
import Definitions.Def_UninformedMG_vdagger

namespace UninformedMG

/-- **Rounding claim in the proof of Theorem 2.1** (p.25 = PDF p.27). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

For opponent policies `ν^1, …, ν^K` let `μ^emp_h(·|s)` attain the minimum in Eq. (1) for every
`(h, s)` (such a policy exists), and let `v†` be the rounded empirical value. Then
1. `v† ∈ V`;
2. `0 ≤ v†_h(s) − V^emp_h(s)/H ≤ (H − h + 1)/(HK)` for every `h ≥ 2` and `s ∈ S_h`;
3. `∑_a μ^emp_h(a|s) Y^k_{h,s,v†,a} ≤ v†_h(s)` for every episode `k`, `h ≥ 2` and `s ∈ S_h`;
4. `∑_a μ^emp_1(a|s) Y^k_{1,s,v†,a} ≤ V^emp_1(s)/H + (H − 1)/(HK)` for every `k` and `s ∈ S_1`.

**Formalization Note.** Lean layer `h` is paper step `h + 1`, so "h ≥ 2" is `0 < h.val` and the
bound `(H − h + 1)/(HK)` is `(H − h.val)/(HK)`; the clause at the terminal layer is the base case. -/
theorem vdagger_rounding {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H)
    (ν : Fin K → OPolicy G) (hν : ∀ j, IsOPolicy G (ν j)) :
    (∃ μe : LPolicy G, IsLPolicy G μe ∧ ∀ (h : Fin H) s,
      ⨆ j : Fin K, stageVal G h (μe h s) (ν j h s) (empValue G ν h.succ) s =
        empValue G ν h.castSucc s) ∧
    ∀ μe : LPolicy G, IsLPolicy G μe → (∀ (h : Fin H) s,
      ⨆ j : Fin K, stageVal G h (μe h s) (ν j h s) (empValue G ν h.succ) s =
        empValue G ν h.castSucc s) →
      (∃ n : GridPt G K, gridVal G K n = vdagger G ν μe) ∧
      (∀ (h : Fin (H + 1)) (s : G.St h), 0 < h.val →
        0 ≤ vdagger G ν μe h s - empValue G ν h s / (H : ℝ) ∧
        vdagger G ν μe h s - empValue G ν h s / (H : ℝ) ≤ ((H : ℝ) - h.val) / ((H : ℝ) * K)) ∧
      (∀ (k : Fin K) (h : Fin H) (s : G.St h.castSucc), 0 < h.val →
        ∑ a, μe h s a * Ytab G (ν k) (vdagger G ν μe) h s a ≤ vdagger G ν μe h.castSucc s) ∧
      (∀ (k : Fin K) (h : Fin H), h.val = 0 → ∀ s : G.St h.castSucc,
        ∑ a, μe h s a * Ytab G (ν k) (vdagger G ν μe) h s a ≤
          empValue G ν h.castSucc s / (H : ℝ) + ((H : ℝ) - 1) / ((H : ℝ) * K)) := by sorry

end UninformedMG
