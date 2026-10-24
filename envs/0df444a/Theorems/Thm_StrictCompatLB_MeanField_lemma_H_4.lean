-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_H_4
-- name    : StrictCompatLB.MeanField.lemma_H_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:05.176556+00:00
-- url     : https://prove2.me/theorems/6417749f-bf7b-46d3-9e8e-aba280ce7156
-- title:
--   Lemma H.4 — the sets C_Γ are petite
-- statement:
--   Let $0<\lambda<1$ and $d\ge1$. For every $N$, every compatibility graph $G_N$ and every $\Gamma\ge0$, the set
--   $$C_\Gamma=\Big\{z\in\mathcal S_N:\sum_{i=1}^\infty Q_i(z)\le\Gamma\Big\}$$
--   is a petite set (Definition H.3) for the uniformised JSQ(d) chain on $G_N$.
--
--   Together with the drift condition of Lemma H.5 this is the input of the Foster–Lyapunov criterion for positive Harris recurrence.
--
--   **Formalization Note** No condition on the graph is assumed. The $n$-step probabilities are those of the uniformised chain, with $n=0$ allowed in the sampling distribution $a$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 49, Lemma H.4; p. 48, (H.10); p. 49, Definition H.3

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma H.4 (p. 49). For every `N`, every graph `G_N` and every `Γ ≥ 0`, the set
`C_Γ = {z : ∑_{i ≥ 1} Q_i(z) ≤ Γ}` of (H.10) is petite (Definition H.3) for the uniformised
JSQ(d) chain. -/
theorem lemma_H_4 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) :
    IsPetite (jsqdKernel lam d M G N) (CGamma N Γ) := by sorry

end StrictCompatLB.MeanField
