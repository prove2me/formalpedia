-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_8
-- name    : SwitchbackExp.Design.lemma_EC_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:43.771986+00:00
-- url     : https://prove2.me/theorems/5f80bc46-6c8b-434e-b52f-e16d5e248ca7
-- title:
--   Lemma EC.8, p. ec10 — a risk-minimizing fair-coin design at 𝕐± has t_{k+1} − t_{k−1} ≥ m for all k ∈ [K]
-- statement:
--   Let $B>0$, $m<T$, $\mathbb Y=\mathbb Y^+$ or $\mathbb Y=\mathbb Y^-$, and let $\mathbb T=\{t_0=1<t_1<\dots<t_K\}$ be regular randomization points that are optimal with fair coins against $\mathbb Y$ (as in Lemma EC.7). Then, with $t_{K+1}=T+1$,
--   $$t_{k+1}-t_{k-1}\ge m\qquad\text{for all }k\in[K]=\{1,\dots,K\}.$$
--
--   Lemma EC.8 says that no window of $m+1$ consecutive periods contains more than three randomization points of an optimal design.
--
--   **Formalization Note** "Optimal design" is read with fair coins and the fixed $\mathbb Y=\mathbb Y^\pm$, as in Lemma EC.7. No restriction on $T$ is added here.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.8, p. ec10; proof EC.3.5.2

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.8 (p. ec10): a regular point set that minimizes the fair-coin risk at `𝕐 = 𝕐⁺` or `𝕐⁻`
has `t_{k+1} − t_{k−1} ≥ m` for every `k ∈ [K]` (with `t_{K+1} = T + 1`). -/
theorem lemma_EC_8 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B)
    (Y : Outcomes) (hYpm : Y = Yplus B ∨ Y = Yminus B) (P : Finset ℕ)
    (hP : IsRegularPoints T P)
    (hopt : ∀ P', IsRegularPoints T P' → risk m T P half Y ≤ risk m T P' half Y) :
    ∀ k : ℕ, 1 ≤ k → k ≤ P.card - 1 → tpt P T (k - 1) + m ≤ tpt P T (k + 1) := by sorry

end SwitchbackExp.Design
