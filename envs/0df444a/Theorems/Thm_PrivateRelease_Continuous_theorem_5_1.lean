-- Prove2me | Theorems.Thm_PrivateRelease_Continuous_theorem_5_1
-- name    : PrivateRelease.Continuous.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:44.518776+00:00
-- url     : https://prove2.me/theorems/cab5bc9e-80c0-46ff-87ec-7caf781e5747
-- title:
--   Theorem 5.1 — no ε-DP mechanism answers median queries usefully with positive probability on every real-valued database
-- statement:
--   Following the paper (p. 14), "we say that a mechanism answers a median query $M$ usefully if it outputs a real value $r$ such that $r$ falls within the $50-\delta, 50+\delta$ percentile of points in database $D$ for some $\delta < 50$." Write $\theta = \delta/100$.
--
--   Let $n \ge 1$, let $0 \le \theta < 1/2$ and let $\varepsilon \in \mathbb R$. Let $A$ be a randomized mechanism that maps each real-valued database $z \in \mathbb R^n$ to a probability distribution $A(z)$ on $\mathbb R$ (with its Borel sets), and suppose $A$ is $\varepsilon$-differentially private: for all databases $z, z'$ differing in exactly one entry and every Borel set $S \subseteq \mathbb R$,
--   $$
--   \Pr[A(z) \in S] \le e^{\varepsilon} \Pr[A(z') \in S].
--   $$
--   Then there is a database $z \in \mathbb R^n$ on which the output of $A$ is a $\theta$-percentile point of $z$ with probability zero:
--   $$
--   \exists\, z \in \mathbb R^n:\qquad \Pr_{r \sim A(z)}\Big[\#\{i : z_i \le r\} \ge (\tfrac12-\theta)n \ \text{ and }\ \#\{i : z_i \ge r\} \ge (\tfrac12-\theta)n\Big] = 0 .
--   $$
--
--   This is the paper's impossibility result for continuous data domains: a private mechanism with real outputs cannot locate the median of every real-valued database, even approximately and even with small positive probability. It is the step to which the impossibility for interval queries (Corollary 5.2) is reduced.
--
--   **Formalization Note.** Neighbours are databases differing in one coordinate (`PrivLearn.Generic.Neighbors`); the paper's "$|D \Delta D'| \le 1$" is read as replace-one. The hypothesis $n \ge 1$ is implicit in the paper (its database $D_0$ "containing $n$ points"); at $n = 0$ the percentile set is all of $\mathbb R$ and the statement fails. The probability-measure hypothesis is needed because the zero measure is differentially private. The output space is $\mathbb R$ with its Borel σ-algebra.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 14, Theorem 5.1 (and the definition sentence preceding it)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivateRelease_Continuous_Queries

open MeasureTheory PrivLearn.Generic

namespace PrivateRelease.Continuous

theorem theorem_5_1 (n : ℕ) (A : (Fin n → ℝ) → Measure ℝ) (ε θ : ℝ)
    (hn : 1 ≤ n) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hA : ∀ z, IsProbabilityMeasure (A z)) (hdp : IsDP A ε) :
    ¬ AnswersMedianUsefully A θ := by sorry

end PrivateRelease.Continuous
