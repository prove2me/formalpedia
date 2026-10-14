-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_2
-- name    : PigeonholeDesign.Upper.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:03.026932+00:00
-- url     : https://prove2.me/theorems/411ce208-a474-4e7e-bf2a-22fabfa5522c
-- title:
--   Lemma 2 — on [0,1], the completely randomized design has worst-case expected discrepancy Θ(T^{1/2})
-- statement:
--   Consider one continuous covariate ($p=1$, $q=0$) with covariates in $[0,1]$. There are constants $0<c\le C$ and a threshold $T_0$ such that for every even $T\ge T_0$:
--
--   1. for every arrival sequence $x\in[0,1]^T$,
--   $$\mathrm{ALG}^{\mathsf C}(x)\le C\sqrt T;$$
--   2. some arrival sequence $x\in[0,1]^T$ has
--   $$\mathrm{ALG}^{\mathsf C}(x)\ge c\sqrt T.$$
--
--   That is, the worst-case expected discrepancy of the completely randomized design is $\Theta(T^{1/2})$. This is the benchmark the pigeonhole design improves upon, and its upper half is used in Component 2 of the proof of Lemma 3.
--
--   **Formalization Note** "$\Theta(T^{1/2})$" is read as both bounds, with $c$, $C$ and $T_0$ chosen before $T$ and the instance. The printed proof of the upper half relies on Lemma EC.6 (that $x^*$ maximizes $\mathrm{ALG}^{\mathsf C}$), which is false (for $T=4$, $x=(0,1,1,1)$ gives $1>2/3=\mathrm{ALG}^{\mathsf C}(x^*)$); the statement itself is true and is stated here as printed.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 14, Lemma 2 (proof p. ec7)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem lemma_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
          crdExp x ≤ C * Real.sqrt T) ∧
      (∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * Real.sqrt T ≤ crdExp x) := by sorry

end PigeonholeDesign.Upper
