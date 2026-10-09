-- Prove2me | Theorems.Thm_SBMThreshold_Main_lemma_3_7
-- name    : SBMThreshold.Main.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:40.561672+00:00
-- url     : https://prove2.me/theorems/4838c909-915d-4648-961f-e50031d0a95b
-- title:
--   Lemma 3.7, p. 14 — there are κ > 0 and ε > 0 with P[Ψ⁺_R ≥ ξκs^R] ≥ 1/2 + 2ε
-- statement:
--   Let $a,b>0$, $d=(a+b)/2$ and $s=(a-b)/2$, and assume $s>0$ and $s^2>d$. Let $T$ be a Galton–Watson tree with $\mathrm{Poisson}(d)$ offspring rooted at $\rho$, labelled by $\eta^+$: the root has label $+1$, and each child independently keeps its parent's label with probability $a/(a+b)$ and takes the opposite label otherwise. Let $\Psi^+_R=\sum_{v\in S_R(\rho)}\eta^+_v$ be the sum of the labels at depth $R$, and let $\xi$ be uniform on $[-1,1]$ and independent of the tree.
--
--   Then there exist $\kappa>0$, $\varepsilon>0$ and $R_0$ such that for every $R\ge R_0$
--   $$
--   \mathbb P\bigl[\Psi^+_R\ge\xi\,\kappa\,s^R\bigr]\ge\frac12+2\varepsilon .
--   $$
--
--   Since the unlabelled-root version satisfies $\mathbb P[\Psi_R\ge\xi\kappa s^R]=\tfrac12$ by symmetry, the lemma says that the depth-$R$ label sum, compared with an independent random threshold of scale $s^R$, carries a bias towards the root's label that does not vanish as $R$ grows. This is the estimate that lets the algorithm's local statistic recover the label of a vertex with probability bounded away from $\tfrac12$.
--
--   **Formalization Note** The hypothesis $s>0$ is the standing assumption of §3.3.1 ("For notational simplicity, we will assume for now that $s>0$", p. 13); $s^2>d$ is the hypothesis of Theorem 2.1, under which the section works. The page leaves the range of $R$ implicit; its proof bounds a $\liminf_{R\to\infty}$, and the algorithm uses $R=2\lceil\log\log\log\log n\rceil\to\infty$, so the statement is made for all sufficiently large $R$, with $\kappa$ and $\varepsilon$ chosen before $R_0$ and $R$. The tree enters only through the law of $\Psi^+_R=Z^+_R-Z^-_R$, encoded by the two-type Poisson generation chain of the definition file.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 14, Lemma 3.7, display (10); standing assumption s > 0 of §3.3.1, p. 13

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Branching

open Filter Topology

namespace SBMThreshold.Main

/-- Lemma 3.7 (p. 14): for fixed `a, b > 0` with `s > 0` (standing in §3.3.1) and `s² > d`, there
are `κ > 0` and `ε > 0` such that `P[Ψ⁺_R ≥ ξ κ s^R] ≥ 1/2 + 2ε` for all sufficiently large `R`,
where `ξ` is uniform on `[-1, 1]` and independent of the tree. -/
theorem lemma_3_7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < sPar a b)
    (hKS : dPar a b < sPar a b ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      1 / 2 + 2 * ε ≤ psiPlusProb a b κ R := by sorry

end SBMThreshold.Main
