-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_proposition_EC_1
-- name    : PigeonholeDesign.Upper.proposition_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:27.449811+00:00
-- url     : https://prove2.me/theorems/73ff2171-4106-4e6f-8740-b0acc812c196
-- title:
--   Proposition EC.1 — a single pigeonhole on [0,1] gives expected discrepancy O(T^{1/2})
-- statement:
--   Consider one continuous covariate ($p=1$, $q=0$) and the pigeonhole design with the single pigeonhole $\mathcal P(S)=\{[0,1]\}$. There is a constant $C>0$ such that for every even $T$ and every arrival sequence $x\in[0,1]^T$,
--   $$\mathbb E\bigl[d_{A,B}\bigr]\ \le\ C\sqrt T .$$
--
--   With a single pigeonhole the design pairs consecutive subjects with opposite random assignments. Applied inside one pigeonhole of length $\ell$, the bound scales to $c\,\ell\sqrt{n}$ for $n$ subjects, which is how Component 1 of the proof of Lemma 3 uses it.
--
--   **Formalization Note** "On the order of $O(T^{1/2})$" is read as a uniform constant $C$ chosen before $T$ and $x$; no threshold is needed since the bound holds for every even $T$. The expectation is the average over all $2^T$ coin vectors.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec10 (PDF p. 48), Proposition EC.1

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem proposition_EC_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        phdExp (fun _ : ℝ => ()) x ≤ C * Real.sqrt T := by sorry

end PigeonholeDesign.Upper
