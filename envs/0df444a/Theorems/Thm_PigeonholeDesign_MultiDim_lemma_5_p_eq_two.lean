-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_lemma_5_p_eq_two
-- name    : PigeonholeDesign.MultiDim.lemma_5_p_eq_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:36:13.803743+00:00
-- url     : https://prove2.me/theorems/f057685c-98e1-4568-816f-71b2aa2e7e92
-- title:
--   Lemma 5 (p = 2) — one subject per grid cell: the completely randomized design has expected discrepancy O(T^{1/2} log T)
-- statement:
--   Let $p=2$ and let $T=m^2$ be even. Split $[0,1]^2$ into the $T$ squares of edge $1/m=T^{-1/2}$, and let $x=(x_1,\dots,x_T)$ place exactly one subject in each square (the family $\mathcal X$). Then the expected discrepancy of the completely randomized design is
--   $$\mathrm{ALG}^C(x)=O\big(T^{\frac{p-1}{p}}\log T\big)=O\big(T^{1/2}\log T\big):$$
--   there are $C>0$ and $T_0$ such that $\mathrm{ALG}^C(x)\le C\,T^{1/2}\log T$ for every even $T\ge T_0$ and every $x\in\mathcal X^{(T)}$.
--
--   Lemma 5 is the paper's bound for a random balanced labelling of a full grid; Component 2 of Theorem 9 applies it to the unmatched subjects.
--
--   **Formalization Note** $C$ and $T_0$ are absolute and come before $T$ and $x$. The cells are $[k/m,(k+1)/m)$ on each axis with the last one closed. The printed proof (pp. ec18–ec20) reaches only $\sqrt2\sqrt{T\log T}\,\log T$, a $(\log T)^{3/2}$ rate; the statement here is Lemma 5's own $\log T$ rate, not the weaker rate of its printed proof.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 26, Lemma 5 (case p = 2); family 𝒳 p. 25

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.MultiDim

theorem lemma_5_p_eq_two :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ m T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → EuclideanSpace ℝ (Fin 2), InGridFamily m x →
        PigeonholeDesign.Upper.crdExp x ≤ C * (T : ℝ) ^ (((2 : ℝ) - 1) / 2) * Real.log T := by sorry

end PigeonholeDesign.MultiDim
