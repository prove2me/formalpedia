-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_1
-- name    : SwitchbackExp.Design.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:25.447947+00:00
-- url     : https://prove2.me/theorems/8a96bcf2-c6bf-49ab-afce-da107bdb812d
-- title:
--   Lemma 1, p. 12 — 𝕐⁺ and 𝕐⁻ dominate every admissible 𝕐, strictly for m ≥ 1 unless 𝕐 = 𝕐± on the reduced outcomes
-- statement:
--   Let $B>0$, $m<T$, and let $(\mathbb T,\mathbb Q)$ be a regular switchback design with $q_{t_k}\in(0,1)$. Let $\mathbb Y$ satisfy Assumptions 1–3 with bound $B$. Let $\mathbb Y^+$ ($\mathbb Y^-$) be the outcomes identically equal to $B$ ($-B$). Then:
--
--   1. $\mathbb Y^+$ and $\mathbb Y^-$ satisfy Assumptions 1–3;
--   2. the extreme outcomes dominate:
--   $$r(\eta_{\mathbb T,\mathbb Q},\mathbb Y^+)\ge r(\eta_{\mathbb T,\mathbb Q},\mathbb Y),\qquad r(\eta_{\mathbb T,\mathbb Q},\mathbb Y^-)\ge r(\eta_{\mathbb T,\mathbb Q},\mathbb Y);$$
--   3. if $m\ge1$ and there are periods $t,t'\in\{m+1,\dots,T\}$ with $(Y_t(\mathbf 1_{m+1}),Y_t(\mathbf 0_{m+1}))\ne(B,B)$ and $(Y_{t'}(\mathbf 1_{m+1}),Y_{t'}(\mathbf 0_{m+1}))\ne(-B,-B)$, then both inequalities are strict.
--
--   Lemma 1 reduces the inner maximization of the minimax problem (6) to evaluating the risk at $\mathbb Y^+$ (or $\mathbb Y^-$).
--
--   **Formalization Note** "$\mathbb Y\ne\mathbb Y^+$" is read on the reduced outcomes $(Y_t(\mathbf 1_{m+1}),Y_t(\mathbf 0_{m+1}))_{t\in\{m+1:T\}}$, which is all the page's definition of $\mathbb Y^\pm$ fixes and all the risk depends on; read over whole outcome functions the strictness claim would be false. The page states the strictness claim for every $m$, but it is false at $m=0$: with $T=2$, $\mathbb T=\{1,2\}$, fair coins, $Y_1\equiv B$ and $Y_2\equiv-B$, the risk equals $r(\eta_{\mathbb T,\mathbb Q},\mathbb Y^+)=2B^2$ (at $m=0$ periods in different blocks have independent error terms, so block-wise signs tie with $\mathbb Y^+$). The strictness clause therefore carries the hypothesis $m\ge1$; for $m\ge1$ consecutive periods share a determining randomization point, which is what makes the inequalities strict. The non-strict domination, which is what the minimax reduction uses, is stated for every $m$.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma 1, p. 12 (𝕐± defined on p. 12); proof EC.3.3.1, pp. ec8–ec9

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma 1 (p. 12): under Assumptions 1–3, `𝕐⁺` and `𝕐⁻` are admissible and dominate every admissible
`𝕐`; for `m ≥ 1` the domination is strict unless the reduced outcomes `(Y_t(1_{m+1}), Y_t(0_{m+1}))`,
`t ∈ {m+1 : T}`, are those of `𝕐⁺` or of `𝕐⁻`. The page states strictness for every `m`; at `m = 0` it
fails (`T = 2`, `𝕋 = {1, 2}`, fair coins, `Y_1 ≡ B`, `Y_2 ≡ −B` has risk `2B² = r(𝕐⁺)`), so the
strictness clause carries `1 ≤ m` (trap 30). -/
theorem lemma_1 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes) (hY : Admissible m T B Y) :
    (Admissible m T B (Yplus B) ∧ Admissible m T B (Yminus B)) ∧
    risk m T P q Y ≤ risk m T P q (Yplus B) ∧ risk m T P q Y ≤ risk m T P q (Yminus B) ∧
    (1 ≤ m → (∃ t ∈ Finset.Icc (m + 1) T, Y1 Y t ≠ B ∨ Y0 Y t ≠ B) →
      (∃ t ∈ Finset.Icc (m + 1) T, Y1 Y t ≠ -B ∨ Y0 Y t ≠ -B) →
      risk m T P q Y < risk m T P q (Yplus B) ∧ risk m T P q Y < risk m T P q (Yminus B)) := by sorry

end SwitchbackExp.Design
