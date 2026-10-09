-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_multiplicative_hellinger
-- name    : StatComplexityDM.LowerBound.multiplicative_hellinger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:43.126649+00:00
-- url     : https://prove2.me/theorems/26625dac-5e61-42d2-8eb4-cfb8f8cd95d0
-- title:
--   Lemma A.11, (94)–(95), p. 72 — multiplicative Pinsker-type inequality for Hellinger distance
-- statement:
--   Let $P$ and $Q$ be probability distributions on a finite set $\mathcal X$, and let $D^2_{\mathrm H}(P,Q)=\sum_x(\sqrt{P(x)}-\sqrt{Q(x)})^2$ be the squared Hellinger distance. Let $h:\mathcal X\to\mathbb R$ satisfy $0\le h(x)\le R$ at every $x$ charged by $P$ or by $Q$. Then
--
--   $$
--   \bigl|\mathbb E_P[h]-\mathbb E_Q[h]\bigr|\le\sqrt{2R\,(\mathbb E_P[h]+\mathbb E_Q[h])\,D^2_{\mathrm H}(P,Q)}
--   \qquad\text{and}\qquad
--   \mathbb E_P[h]\le 3\,\mathbb E_Q[h]+4R\,D^2_{\mathrm H}(P,Q).
--   $$
--
--   This change-of-measure inequality loses only a multiplicative constant rather than an additive $\sqrt{D^2_{\mathrm H}}$ term, which gives faster rates when the means are small.
--
--   **Formalization Note** The sample space is finite; "almost surely under $P$ and $Q$" is the range condition on the union of the supports. Hellinger distance has no factor $\tfrac12$, as in (5), p. 10.
-- source:
--   arXiv:2112.13487v3, Lemma A.11, (94)–(95), p. 72

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- Lemma A.11, (95), p. 72: the multiplicative Hellinger inequality. -/
theorem multiplicative_hellinger {Ω : Type*} [Fintype Ω]
    (P Q : Ω → ℝ) (hP : IsDist P) (hQ : IsDist Q) (h : Ω → ℝ) (R : ℝ)
    (hRangeP : ∀ ω, P ω ≠ 0 → 0 ≤ h ω ∧ h ω ≤ R)
    (hRangeQ : ∀ ω, Q ω ≠ 0 → 0 ≤ h ω ∧ h ω ≤ R) :
    |(∑ ω, P ω * h ω) - (∑ ω, Q ω * h ω)| ≤
        Real.sqrt (2 * R * ((∑ ω, P ω * h ω) + (∑ ω, Q ω * h ω)) *
          hellingerSq P Q) ∧
      (∑ ω, P ω * h ω) ≤ 3 * (∑ ω, Q ω * h ω) +
        4 * R * hellingerSq P Q := by sorry

end StatComplexityDM.LowerBound
