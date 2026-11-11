-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_8_2
-- name    : SubexpPermanent.Main.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:03:17.835409+00:00
-- url     : https://prove2.me/theorems/b88307d0-ed7b-4390-a6ce-f45de958f397
-- title:
--   Lemma 8.2 — a point $z\in X=[-W,0]^m$ with $F_{\hat A}(z,\log\Lambda)\le\mathrm{OPT}_{\hat A}(\log\Lambda)+\varepsilon n/64$
-- statement:
--   Fix a bipartite graph with $n\ge1$ vertices on each side and nonempty edge set $E$ in which every edge belongs to a perfect matching, $m=|E|$, and $\theta\in\mathbb Q^E$. Let $\hat A_{ij}=e^{\theta_{ij}}$ on $E$ and $0$ elsewhere. Let $\Lambda\ge1$ and $0<\varepsilon\le1$ be rational, and set
--   $$\tau=\frac{\varepsilon}{128n},\qquad W=8+\Big\lceil\log_2\Big(1+\frac\Lambda\tau\Big)\Big\rceil\quad(34),\qquad a=\log\Lambda,\qquad X=[-W,0]^m .$$
--   Then there is a point $z\in X$ with
--   $$F_{\hat A}(z,a)\le\mathrm{OPT}_{\hat A}(a)+\frac{\varepsilon n}{64}.$$
--   This lets the projected subgradient method of §8 run over the box $X$ while losing only $\varepsilon n/64$.
--
--   Differences from the source:
--
--   - encoding: a bipartite graph with n vertices on each side and edge set E, every edge in a perfect matching → E₀ : Finset (Fin n × Fin n), nonempty, with every pair in E₀ lying on a permutation σ with (k, σ k) ∈ E₀ for all k; Â = hatMatrix E₀ θ; reason: rows and columns are the two sides; Â is positive exactly on E₀, so the edge set E of Â is E₀
--   - encoding: X = [−W, 0]^m ⊆ ℝ^E → {z : Edges Â → ℝ | ∀ e, −W ≤ z_e ≤ 0}; reason: the same box
--   - encoding: log₂ and ⌈·⌉ → Real.logb 2 and Int.ceil; reason: the definitions
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 29, Lemma 8.2 (setting: §8, p. 29, eq. (34))

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective

namespace SubexpPermanent.Main

/-- Lemma 8.2 (a nearly optimal point in `X`), p. 29, in the setting of §8: a bipartite graph
with `n ≥ 1` vertices on each side and nonempty edge set `E₀ ⊆ [n] × [n]` in which every edge
lies in a perfect matching, `θ ∈ ℚ^{E₀}`, `Â = e^θ` on `E₀` and `0` elsewhere, rationals
`Λ ≥ 1` and `0 < ε ≤ 1`, `τ = ε/(128 n)`, `W = 8 + ⌈log₂(1 + Λ/τ)⌉` (34), `a = log Λ`,
`X = [−W, 0]^E`. -/
theorem lemma_8_2 {n : ℕ} (hn : 1 ≤ n) (E₀ : Finset (Fin n × Fin n)) (hE₀ : E₀.Nonempty)
    (hpm : ∀ p ∈ E₀, ∃ σ : Equiv.Perm (Fin n), σ p.1 = p.2 ∧ ∀ k, (k, σ k) ∈ E₀)
    (θ : E₀ → ℚ) (Λ ε : ℚ) (hΛ : 1 ≤ Λ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let τ : ℝ := (ε : ℝ) / (128 * n)
    let W : ℝ := 8 + (⌈Real.logb 2 (1 + (Λ : ℝ) / τ)⌉ : ℝ)
    ∃ z : Edges (hatMatrix E₀ θ) → ℝ,
      (∀ e, -W ≤ z e ∧ z e ≤ 0) ∧
      F (hatMatrix E₀ θ) z (Real.log Λ) ≤ OPT (hatMatrix E₀ θ) (Real.log Λ) + (ε : ℝ) * n / 64 := by sorry

end SubexpPermanent.Main
