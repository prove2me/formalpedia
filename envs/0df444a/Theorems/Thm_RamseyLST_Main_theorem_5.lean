-- Prove2me | Theorems.Thm_RamseyLST_Main_theorem_5
-- name    : RamseyLST.Main.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:05.233207+00:00
-- url     : https://prove2.me/theorems/12ad3c7d-585f-4830-804e-d30b5067750e
-- title:
--   Theorem 5 — strong $(O(t), 1-1/t)$-Ramsey embedding of any finite metric space into an HST
-- statement:
--   There is an absolute constant $c_0$ such that the following holds. Let $(X,d)$ be a finite metric space and let $t>1$. Then there are an HST $U$ (an ultrametric given by a finite labelled tree, Definition 4) on a finite set of leaves, an embedding $f:X\to U$ and a core $Z\subseteq X$ such that $f$ is a strong $(c_0t,\,1-1/t)$-Ramsey embedding with core $Z$. That is, $f$ is injective and non-contractive, $|Z|\ge|X|^{1-1/t}$, and
--
--   $$d_U(f(x),f(y))\le c_0\,t\;d(x,y)\qquad\text{for every }x\in Z\text{ and every }y\in X.$$
--
--   This is the strong form of the metric Ramsey theorem ([Bar21, ACE+20]). It is the first step of the construction of the candidate core (Lemma 8).
--
--   Differences from the source:
--   - encoding: O(t) distortion → c₀ · t for one constant c₀ chosen before X and t; reason: explicit constant for O(·)
--   - encoding: an HST U → a finite type Q with an `HST Q` labelled tree (Definition 4, labels non-increasing, i.e. a 1-HST), and the distance δ(lca); reason: Definition 4 with µ = 1; the target of a finite space can be taken finite
--   - reading: (a deterministic construction of) an embedding f → existence of the embedding f; reason: the parenthetical names the method of [Bar21, ACE+20]; no computational model is fixed, and the mathematical claim is the existence of f
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 14 (PDF 18), Theorem 5

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_HST

namespace RamseyLST.Main

/-- Theorem 5 (p. 14, [Bar21, ACE+20]): there is an absolute constant `c₀` such that for every
finite metric space `(X, d)` and every `t > 1` there are an HST `U` (a finite labelled tree as in
Definition 4) and an embedding `f : X → U` which is a strong `(c₀ t, 1 − 1/t)`-Ramsey embedding. -/
theorem theorem_5 :
    ∃ c₀ : ℝ, ∀ (P : Type) [Fintype P] (d : P → P → ℝ), IsMetric d → ∀ t : ℝ, 1 < t →
      ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (U : HST Q) (f : P → Q) (Z : Finset P),
        IsStrongRamseyEmbedding d U.dist f Z (c₀ * t) (1 - 1 / t) := by sorry

end RamseyLST.Main
