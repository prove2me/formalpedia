-- Prove2me | Theorems.Thm_UninformedMG_divergence_uniform_start
-- name    : UninformedMG.divergence_uniform_start
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:27.660714+00:00
-- url     : https://prove2.me/theorems/af5258da-bbae-4836-93c9-155a15e149da
-- title:
--   p.16 — uniform start: $D_{\mathcal H_{\mathrm{res}}}(z^{v,x}\|z^1)\le H\log N+S\log A$
-- statement:
--   Let $\mathcal V$ be the candidate grid of Eq. (19), $N=|\mathcal V|$, and let $A$ satisfy $|A_h|\le A$ for every step. For a candidate $v\in\mathcal V$ and a mixed Markov policy $x$, let $z^{v,x}_{h,s,v',a}=\mathbf 1\{v'=v\}x_h(a\mid s)$ and let $z^1$ be the uniform start (6). Then
--   $$D_{\mathcal H_{\mathrm{res}}}(z^{v,x}\,\|\,z^1)\le H\log N+S\log A.$$
--
--   This bound is the initial divergence in the OMD analysis of Lemma B.3. Scaling the candidate entropy by $H$ instead of $S$ in (20) is what makes the first term $H\log N$.
--
--   Differences from the source:
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - encoding: z ∈ 𝒵 → the pair (w, π) of Eq. (4); reason: every z ∈ 𝒵 is w·π and every quantity used is unchanged by π at w(v) = 0
--   - encoding: H ≥ 2 (Section 2) and K ≥ 1 implicit → explicit hypotheses 2 ≤ H, 1 ≤ K; reason: standing assumptions of Section 2 and of the model
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Appendix B.1.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_divRes

namespace UninformedMG

/-- **Uniform-start divergence bound** (Appendix B.1.1, p.16 = PDF p.18). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

For a candidate `v ∈ V` and a mixed Markov policy `x`, let `z^{v,x}_{h,s,v',a} = 1{v' = v} x_h(a|s)`.
Uniform initialization gives `D_{ℋres}(z^{v,x} ‖ z¹) ≤ H log N + S log A`, with `N = |V|` for the grid
`V` of Eq. (19).

**Formalization Note.** `A` is any number with `|A_h| ≤ A` for every step (the paper's
`A = |⋃_h A_h|` is one). `z^{v,x}` is the pair `(1{· = v}, x)`, `z¹` the uniform pair of Eq. (6). -/
theorem divergence_uniform_start {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    (v : (grid G K).C) (x : LPolicy G) (hx : IsLPolicy G x) :
    divRes (grid G K) (cmpW (grid G K) v) (cmpPi (grid G K) x) (unifW (grid G K))
        (unifPi (grid G K)) ≤
      (H : ℝ) * Real.log (Fintype.card (grid G K).C) + (G.numStates : ℝ) * Real.log A := by sorry

end UninformedMG
