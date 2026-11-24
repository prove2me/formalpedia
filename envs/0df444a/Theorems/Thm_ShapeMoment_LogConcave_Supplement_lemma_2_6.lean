-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_Supplement_lemma_2_6
-- name    : ShapeMoment.LogConcave.Supplement.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:09:43.395116+00:00
-- url     : https://prove2.me/theorems/e3a55f51-32e5-427d-9c33-e25a8a4b52d1
-- title:
--   Lemma 2.6, p. 7 — a distribution is IFR iff its tail sequence is log-concave
-- statement:
--   Let $x=(x_1,\dots,x_n)$ be a distribution on $\{1,\dots,n\}$ in the sense of p. 5 of the paper, a nonnegative vector $x_j\ge 0$ (the normalization $\sum_j x_j=1$ comes from the moment constraint $q_0=1$, not from the word "distribution", and the lemma does not need it). Let $\bar F_j=\sum_{k=j}^n x_k$ be its tail probabilities. Then
--   $$x\ \text{has an increasing failure rate}\iff(\bar F_1,\dots,\bar F_n)\ \text{is log-concave.}$$
--   Here IFR means that the failure rates $r_j=x_j/\bar F_j$ are non-decreasing on the indices where they are defined ($\bar F_j>0$), and log-concavity of the tail sequence is Definition 2.1 for a nonnegative sequence: no internal zeros and $\bar F_{j-1}\bar F_{j+1}\le\bar F_j^2$ for $j\in(1,n)$.
--
--   The lemma is what turns the IFR moment problem (DMP-IFR) into (DMP-IFR′), a problem with log-concavity and monotonicity constraints on the tail coordinates, to which Theorem 3.6 applies.
--
--   **Formalization Note** Distributions whose last masses vanish are allowed; there the tail is eventually $0$ and the failure rate is undefined, so it is not compared. Log-concavity of the tail sequence does not require its entries to sum to $1$.
--
--   Differences from the source:
--
--   - reading: "a distribution x" → x ≥ 0 with no normalization; reason: p. 5 defines a distribution as the nonnegative vector (x_1, …, x_n) representing a measure, and the normalization is imposed separately by the constraint q_0 = 1; both shape classes are invariant under positive scaling
--   - encoding: r_j = x_j / ∑_{k≥j} x_k is non-decreasing → r_j ≤ r_k for j ≤ k whenever the tail at k is positive; reason: the rate is undefined at a zero tail, and the condition excludes only those undefined comparisons
--   - reading: "the tail probability sequence is log-concave", with Definition 2.1 stated for distributions → conditions (i) and (ii) of Definition 2.1 and nonnegativity, without normalization; reason: the tail sequence sums to the mean ∑_j j x_j, not to 1, so the normalization of a distribution cannot be part of the definition applied to it
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 7, Lemma 2.6; Definitions 2.1–2.2, p. 5; proof in Appendix A.3, pp. 24–25

import Definitions.Def_ShapeMoment_LogConcave_Supplement_TailShape

open scoped BigOperators

namespace ShapeMoment.LogConcave.Supplement

theorem lemma_2_6 (n : ℕ) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    IsIFR x ↔ IsLCSeq (tail x) := by sorry

end ShapeMoment.LogConcave.Supplement
