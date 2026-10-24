-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_7
-- name    : SwitchbackExp.Design.lemma_EC_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:40.451588+00:00
-- url     : https://prove2.me/theorems/78e25441-1b07-408c-8d84-0eb4002a6741
-- title:
--   Lemma EC.7, p. ec10 — (for m = 0 or T = nm, n ≥ 4) a risk-minimizing fair-coin design at 𝕐± has t₁ ≥ m + 2 and t_K ≤ T − m
-- statement:
--   Let $B>0$, $m<T$, and suppose $m=0$ or $T=nm$ for some integer $n\ge4$. Let $\mathbb Y=\mathbb Y^+$ or $\mathbb Y=\mathbb Y^-$, and let $\mathbb T=\{t_0=1<t_1<\dots<t_K\}$ be regular randomization points that are optimal with fair coins against $\mathbb Y$, i.e.
--   $$r(\eta_{\mathbb T,1/2},\mathbb Y)\le r(\eta_{\mathbb T',1/2},\mathbb Y)\quad\text{for every regular }\mathbb T'.$$
--   Then
--   $$t_1\ge m+2\qquad\text{and}\qquad t_K\le T-m .$$
--
--   Lemma EC.7 fixes the shape of the first and the last block of an optimal design: each is followed by at least $m$ periods without a coin flip.
--
--   **Formalization Note** "Optimal design of experiment $\mathbb T$" is read, as in the page's EC.3.4–EC.3.5, with the fair coins of Theorem 1 and against the fixed $\mathbb Y=\mathbb Y^\pm$. The hypothesis "$m=0$ or $T=nm$ with $n\ge4$" is **added**: without it the lemma is false, e.g. at $m=1$, $T=3$ both optimal point sets $\{1,2\}$ and $\{1,3\}$ have $t_1\le m+1$ (the page's proof deletes $t_1$, which for $K=1$ leaves the single point $\{1\}$, not a regular design). The added hypothesis is that of the mission's goal theorem.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.7, p. ec10; proof EC.3.5.1, pp. ec11–ec13

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.7 (p. ec10), with the disclosed hypothesis `m = 0 ∨ ∃ n ≥ 4, T = n m`: a regular point set
that minimizes the fair-coin risk at `𝕐 = 𝕐⁺` or `𝕐⁻` has `t₁ ≥ m + 2` and `t_K ≤ T − m`. -/
theorem lemma_EC_7 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B)
    (hmn : m = 0 ∨ ∃ n : ℕ, 4 ≤ n ∧ T = n * m)
    (Y : Outcomes) (hYpm : Y = Yplus B ∨ Y = Yminus B) (P : Finset ℕ)
    (hP : IsRegularPoints T P)
    (hopt : ∀ P', IsRegularPoints T P' → risk m T P half Y ≤ risk m T P' half Y) :
    m + 2 ≤ tpt P T 1 ∧ tpt P T (P.card - 1) + m ≤ T := by sorry

end SwitchbackExp.Design
