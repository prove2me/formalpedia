-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_lemma_5_p_ge_three
-- name    : PigeonholeDesign.MultiDim.lemma_5_p_ge_three
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:36:21.046359+00:00
-- url     : https://prove2.me/theorems/0719055f-a136-4db0-a460-d92f2b7221d5
-- title:
--   Lemma 5 (p ≥ 3) — one subject per grid cell: the completely randomized design has expected discrepancy O(T^{(p−1)/p})
-- statement:
--   Fix $p\ge3$. Let $T=m^p$ be even, split $[0,1]^p$ into the $T$ cubes of edge $1/m=T^{-1/p}$, and let $x=(x_1,\dots,x_T)$ place exactly one subject in each cube (the family $\mathcal X$). Then the expected discrepancy of the completely randomized design is
--   $$\mathrm{ALG}^C(x)=O\big(T^{\frac{p-1}{p}}\big):$$
--   there are $C>0$ and $T_0$, depending only on $p$, with $\mathrm{ALG}^C(x)\le C\,T^{(p-1)/p}$ for every even $T\ge T_0$ and every $x\in\mathcal X^{(T)}$.
--
--   This matches, up to constants, the discrepancy $\Theta(T^{(p-1)/p})$ of the clairvoyant matched-pair design (Theorem 7), so on a full grid random balancing loses nothing in dimension $p\ge3$.
--
--   **Formalization Note** $p$ is fixed first; $C$ and $T_0$ may depend on $p$ and come before $T$ and $x$. Cells are $[k/m,(k+1)/m)$ on each axis, the last closed.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 26, Lemma 5 (case p ≥ 3); family 𝒳 p. 25

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.MultiDim

theorem lemma_5_p_ge_three (p : ℕ) (hp : 3 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ m T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → EuclideanSpace ℝ (Fin p), InGridFamily m x →
        PigeonholeDesign.Upper.crdExp x ≤ C * (T : ℝ) ^ (((p : ℝ) - 1) / p) := by sorry

end PigeonholeDesign.MultiDim
