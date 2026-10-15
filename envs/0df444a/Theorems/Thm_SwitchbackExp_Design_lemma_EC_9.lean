-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_9
-- name    : SwitchbackExp.Design.lemma_EC_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:47.504991+00:00
-- url     : https://prove2.me/theorems/2649a20c-39d0-40ae-bd4a-b607c22d9558
-- title:
--   Lemma EC.9, p. ec11 — under t₁ ≥ m+2, t_K ≤ T−m, t_{k+1} − t_{k−1} ≥ m, the fair-coin risk at 𝕐± is the closed form (EC.8)
-- statement:
--   Let $B>0$, $m<T$, $\mathbb Y=\mathbb Y^+$ or $\mathbb Y=\mathbb Y^-$, and let $\mathbb T=\{t_0=1<t_1<\dots<t_K\}$ be regular randomization points with $t_{K+1}=T+1$ satisfying
--   $$t_1\ge m+2,\qquad t_K\le T-m,\qquad t_{k+1}-t_{k-1}\ge m\ \ \forall k\in[K].$$
--   Then, with fair coins,
--   $$r(\eta_{\mathbb T,1/2},\mathbb Y)=\frac1{(T-m)^2}\Bigl\{4\sum_{k=1}^{K+1}(t_k-t_{k-1})^2+8m(t_K-t_1)+4m^2K-4m^2+4\sum_{k=2}^{K}\bigl[(m-t_k+t_{k-1})^+\bigr]^2\Bigr\}B^2.\qquad\text{(EC.8)}$$
--
--   (EC.8) is the bridge from the risk to the subset selection problem (7) of Theorem 2.
--
--   **Formalization Note** The coins are fair: §EC.3.5 works after "plugging in the optimal probabilities being $1/2$" (EC.3.4.2), and (EC.8) contains no $q$, so it cannot hold for general $\mathbb Q$.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.9, p. ec11, (EC.8); proof EC.3.5.3, pp. ec14–ec21

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.9 (p. ec11), (EC.8): under `t₁ ≥ m + 2`, `t_K ≤ T − m` and `t_{k+1} − t_{k−1} ≥ m` for
`k ∈ [K]`, the fair-coin risk at `𝕐 = 𝕐⁺` or `𝕐⁻` has the closed form (EC.8). -/
theorem lemma_EC_9 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B)
    (Y : Outcomes) (hYpm : Y = Yplus B ∨ Y = Yminus B) (P : Finset ℕ)
    (hP : IsRegularPoints T P)
    (h1 : m + 2 ≤ tpt P T 1) (h2 : tpt P T (P.card - 1) + m ≤ T)
    (h3 : ∀ k : ℕ, 1 ≤ k → k ≤ P.card - 1 → tpt P T (k - 1) + m ≤ tpt P T (k + 1)) :
    risk m T P half Y
      = 1 / ((T : ℝ) - m) ^ 2 *
          (4 * ∑ k ∈ Finset.Icc 1 (P.card - 1 + 1), ((tpt P T k : ℝ) - tpt P T (k - 1)) ^ 2
            + 8 * m * ((tpt P T (P.card - 1) : ℝ) - tpt P T 1)
            + 4 * (m : ℝ) ^ 2 * ((P.card - 1 : ℕ) : ℝ) - 4 * (m : ℝ) ^ 2
            + 4 * ∑ k ∈ Finset.Icc 2 (P.card - 1),
                (max ((m : ℝ) - tpt P T k + tpt P T (k - 1)) 0) ^ 2) * B ^ 2 := by sorry

end SwitchbackExp.Design
