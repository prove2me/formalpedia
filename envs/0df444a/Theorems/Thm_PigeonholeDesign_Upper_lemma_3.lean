-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_3
-- name    : PigeonholeDesign.Upper.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:06.609978+00:00
-- url     : https://prove2.me/theorems/52c0da03-70cf-43a0-99f3-3090d9b210d9
-- title:
--   Lemma 3 — T^η uniform pigeonholes give expected discrepancy O(T^{1/2−η/2} + T^{η/2}(log T)^{1/2})
-- statement:
--   Fix $\eta\in(0,1)$ and consider one continuous covariate ($p=1$, $q=0$) with values in $[0,1]$. Let the pigeonhole design use the uniform pigeonholes
--   $$\mathcal P(S)=\bigl\{[0,T^{-\eta}),\,[T^{-\eta},2T^{-\eta}),\,\dots,\,[1-T^{-\eta},1]\bigr\}.$$
--   Then there are a constant $C>0$ and a threshold $T_0$, depending only on $\eta$, such that for every even $T\ge T_0$ and every arrival sequence $x\in[0,1]^T$ chosen in advance, the expected discrepancy of the design satisfies
--   $$\mathbb E\bigl[d_{A,B}\bigr]\ \le\ C\Bigl(T^{\frac12-\frac\eta2}+T^{\frac\eta2}(\log T)^{\frac12}\Bigr).$$
--
--   This is the main upper bound of the paper for one covariate. The first term comes from subjects matched within a pigeonhole and the second from the balancing of the leftover subjects; at $\eta=1/2$ the bound is $O(T^{1/4}(\log T)^{1/2})$ (Corollary 1), against $\Theta(T^{1/2})$ for the completely randomized design (Lemma 2).
--
--   **Formalization Note** The printed partition has $T^{\eta}$ cells, which is not an integer in general; the formalization uses $K=\lceil T^{\eta}\rceil$ cells of length $1/K\le T^{-\eta}$, the last one closed, which coincides with the printed partition when $T^\eta$ is an integer. The expectation is the average of the discrepancy over all $2^T$ coin vectors (not one run and not the best run), and the bound is uniform over all $x\in[0,1]^T$. "On the order of $O(\cdot)$" is read as $\exists C>0,\exists T_0$ before $T$ and $x$. The logarithm is natural, and $T_0$ also avoids the degenerate values $T\in\{0,1\}$ where $\log T\le0$.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 18, Lemma 3 (proof pp. ec7-ec10)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem lemma_3 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        phdExp (uniformHole ⌈(T : ℝ) ^ η⌉₊) x
          ≤ C * ((T : ℝ) ^ (1 / 2 - η / 2) + (T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T)) := by sorry

end PigeonholeDesign.Upper
