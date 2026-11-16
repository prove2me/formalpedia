-- Prove2me | Theorems.Thm_PersuasionByParts_Known_Supplement_lemma_3_2
-- name    : PersuasionByParts.Known.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:37.2641+00:00
-- url     : https://prove2.me/theorems/fdfa5f59-71b8-4f0f-a9a3-859d85bd89b5
-- title:
--   Lemma 3.2 — Cutoff reduction for a fixed product experiment
-- statement:
--   Let $n\ge1$, let $P=\bigotimes_{i=1}^nP_i$ be a product prior on independent real coordinates with finite means, and let $\Pi$ be one fixed product experiment. For a decision function $g$ (measurable, nondecreasing, $[0,1]$-valued) write $V_\Pi(g)=\mathbb E[g(Y_\Pi)]$, where $Y_\Pi$ is the sum of the coordinate posterior means under $\Pi$, and $V_{\rm joint}(g)=\sup_{\Pi'\text{ joint}}V_{\Pi'}(g)$. For a cutoff $t\in\mathbb R$, $V_\Pi(t)$ and $V_{\rm joint}(t)$ are these quantities for $g=\mathbf 1_{[t,\infty)}$.
--
--   Let $c>0$ and $\alpha\ge1$ be real. If
--
--   $$V_\Pi(t)\ \ge\ c\,V_{\rm joint}(t)^\alpha\qquad\text{for every }t\in\mathbb R,$$
--
--   then
--
--   $$V_\Pi(g)\ \ge\ c\,V_{\rm joint}(g)^\alpha\qquad\text{for every decision function }g.$$
--
--   The same constant $c$ and the same exponent $\alpha$ appear in hypothesis and conclusion. Unlike the reduction for the optimal values $V_{\rm prod}$ (Lemma 2.2 of the mission, which loses a factor $4$), this reduction is for a single experiment that serves all cutoffs simultaneously. It is the last step of the proof of the universal guarantee (Theorem 3.1).
--
--   **Formalization Note** The statement uses the published model `PersuasionByParts.Known.Model`; the experiment is named `E` because `Π` is reserved notation in Lean.
--
--   Differences from the source:
--   - encoding: n ≥ 1 sources (standing assumption of §1.1) → the binder 0 < n; reason: the published model indexes sources by Fin n and keeps positivity as a theorem binder
--   - encoding: V_Π(t) and V_Π(g) for a fixed product experiment Π; V_joint(t), V_joint(g) → productPayoff P E (cutoff t), productPayoff P E g, jointCutoff P t, jointValue P g of the published model; reason: these are the published model's names for exactly these quantities (Definition 1.1)
--   - encoding: the real power V_joint(·)^α with α ≥ 1 → Real.rpow (x ^ α with α : ℝ); reason: the joint values lie in [0, 1], where rpow is the ordinary real power
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 12 / PDF p. 13, Lemma 3.2 (Cutoff reduction for a fixed experiment); model §1.1 and Definition 1.1, printed pp. 1–2 / PDF pp. 2–3

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Supplement

/-- Lemma 3.2, printed p. 12 / PDF p. 13: one fixed product experiment `E`; the same
constant `c > 0` and the same real exponent `α ≥ 1` pass from all cutoffs to all
decision functions, with no loss. -/
theorem lemma_3_2 {n : ℕ} (P : Prior n) (hn : 0 < n) (E : ProductExperiment n)
    (c α : ℝ) (hc : 0 < c) (hα : 1 ≤ α)
    (hcutoff : ∀ t : ℝ, productPayoff P E (cutoff t) ≥ c * jointCutoff P t ^ α) :
    ∀ g : Decision, productPayoff P E g ≥ c * jointValue P g ^ α := by sorry

end PersuasionByParts.Known.Supplement
