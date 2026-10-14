-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_component_2
-- name    : PigeonholeDesign.MultiDim.component_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:38:40.281966+00:00
-- url     : https://prove2.me/theorems/9ca02234-35ff-4d40-98a8-3e270a657ae5
-- title:
--   Proof of Theorem 9, Component 2, pp. ec22–ec24 — the remaining subjects contribute O(T^{(p−1)φ}(log T)^{3/2}) (p = 2), O(T^{(p−1)φ}) (p ≥ 3)
-- statement:
--   In the setting of Theorem 9 ($p\ge2$, finite supports $S_i\subseteq[0,1]$, $\varphi\in(0,1)$, $c>1$, and $m=\lceil c^{-1/p}T^{\varphi}\rceil$ cells per continuous axis), let $R$ be the set of subjects that are not matched: the unmatched subjects among the first $\tau$ together with the last $T-\tau$ subjects. The expected discrepancy between the control and treated subjects of $R$, averaged over all coin vectors, satisfies
--   $$\mathbb E\big[d_{A\cap R,\,B\cap R}\big]=\begin{cases}O\big(T^{(p-1)\varphi}(\log T)^{3/2}\big), & p=2,\\[2pt] O\big(T^{(p-1)\varphi}\big), & p\ge3:\end{cases}$$
--   there are $C>0$ and $T_0$, depending only on $p,q,S,\varphi,c$, such that the bound holds with constant $C$ for every even $T\ge T_0$ and every admissible $x$.
--
--   Together with Component 1 this gives Theorem 9.
--
--   **Formalization Note** Only the conclusion of the component is stated. The printed argument applies Lemma 5 to the unmatched subjects, which occupy distinct cells but do not form a full grid of $\mathcal X$, and treats $q\ge1$ per discrete support although the balancing step is global; the conclusion itself is not affected. The complement of the matched set is balanced, so the discrepancy on it is a genuine perfect matching.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec22–ec24, proof of Theorem 9, Component 2

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_MultiDim_Stopping

namespace PigeonholeDesign.MultiDim

theorem component_2 (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ)
    (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1) (φ c : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → Cov q p, Admissible S x →
        (∑ coin : Fin T → Bool,
            PigeonholeDesign.Upper.discrepancyOn x (PigeonholeDesign.Lower.assign (gridHole (cellsPerAxis p c φ T)) x coin)
              (Finset.univ \ matched (fun t => gridHole (cellsPerAxis p c φ T) (x t))
                (PigeonholeDesign.Lower.assign (gridHole (cellsPerAxis p c φ T)) x coin))) / 2 ^ T
          ≤ C * (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
              (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1) := by sorry

end PigeonholeDesign.MultiDim
