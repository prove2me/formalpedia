-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_worst_resolvability_one_shot
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.worst_resolvability_one_shot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:53:11.38048+00:00
-- url     : https://prove2.me/theorems/17bdab93-f036-4346-9214-73e0ae4abb30
-- title:
--   Worst-input one-shot resolvability bound
-- statement:
--   Let $W:x\mapsto W_x$ be a classical discrete stochastic channel from $X$ to $Y$, and let $p$ be a probability mass function on $X$. Write $W_p(y)=\sum_xp(x)W_x(y)$. All logarithms are natural, $d(P,Q)=\sum_y|P(y)-Q(y)|$ is the full L1 distance, and $D(P\|Q)$ is extended nonnegative KL divergence, infinite on a support mismatch. Zero-mass terms in the defining KL expression contribute zero.
--
--   Assume $X$ is nonempty, let $M\ge1$ be an integer, and let $C>0$. For each input law $p$, let $\epsilon(M,W,p)$ be the infimum of $d(W_\Psi,W_p)$ over positive tuple codebooks of size at most $M$, allowing repeated entries, and set $\epsilon(M,W)=\sup_p\epsilon(M,W,p)$. Then
--   $$
--   \epsilon(M,W)\le 2\sup_p\mathbb P_{p(x)W_x(y)}\{W_x(y)/W_p(y)>C\}+\sqrt{C/M}.
--   $$
--   The supremum ranges over all input laws and lies outside the probability expression. No maximizing law or best codebook is asserted on arbitrary alphabets. This is the uniform approximation bound used in the asymptotic capacity relations.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 6, Unnumbered (17): worst-input resolvability bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.6, (17): input-law supremum OUTSIDE the tail probability;
size<=M is tied to actual positive tuple codes, allowing repetitions. -/
theorem worst_resolvability_one_shot {X Y : Type*} [Nonempty X]
    (W : X → Y → ℝ≥0∞) (hW : IsDiscreteStochastic W)
    (M : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 < C) :
    worstApproximation false M W ≤ ENNReal.ofReal
      (2 * sSup (Set.range (fun p : PMF X => upperLikelihoodMass W p C)) + Real.sqrt (C / M)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
