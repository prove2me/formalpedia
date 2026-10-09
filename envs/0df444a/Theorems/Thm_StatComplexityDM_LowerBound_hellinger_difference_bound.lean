-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_hellinger_difference_bound
-- name    : StatComplexityDM.LowerBound.hellinger_difference_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:39.978041+00:00
-- url     : https://prove2.me/theorems/c4558661-a520-4327-b237-c439c70ea947
-- title:
--   Lemma A.12, (96), p. 72 — Hellinger change of measure for a difference Z = X − Y with |X − Y| ≤ ε
-- statement:
--   Let $P$ and $Q$ be probability distributions on a finite set $\Omega$, and let $X,Y:\Omega\to\mathbb R$ satisfy $X\ge0$, $Y\ge0$ and $|X-Y|\le\varepsilon$ at every point charged by $P$ or by $Q$. Then, for $Z=X-Y$,
--
--   $$
--   \bigl|\mathbb E_P[Z]-\mathbb E_Q[Z]\bigr|\le\sqrt{8\varepsilon\,\bigl(\mathbb E_P[X+Y]+\mathbb E_Q[X+Y]\bigr)\,D^2_{\mathrm H}(P,Q)}.
--   $$
--
--   The bound controls a small difference of two nonnegative quantities, with a leading factor $\varepsilon$ rather than the size of $X$ and $Y$; it is the change-of-measure step of the proof of Theorem 3.2.
--
--   **Formalization Note** The sample space is finite, and the range conditions are imposed on the union of the supports of $P$ and $Q$.
-- source:
--   arXiv:2112.13487v3, Lemma A.12, (96), p. 72

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- Lemma A.12, (96), p. 72, for a finite random variable. -/
theorem hellinger_difference_bound {Ω : Type*} [Fintype Ω]
    (P Q : Ω → ℝ) (hP : IsDist P) (hQ : IsDist Q)
    (X Y : Ω → ℝ) (ε : ℝ)
    (hXP : ∀ ω, P ω ≠ 0 → 0 ≤ X ω ∧ 0 ≤ Y ω ∧ |X ω - Y ω| ≤ ε)
    (hXQ : ∀ ω, Q ω ≠ 0 → 0 ≤ X ω ∧ 0 ≤ Y ω ∧ |X ω - Y ω| ≤ ε) :
    |(∑ ω, P ω * (X ω - Y ω)) - (∑ ω, Q ω * (X ω - Y ω))| ≤
      Real.sqrt (8 * ε *
        ((∑ ω, P ω * (X ω + Y ω)) + (∑ ω, Q ω * (X ω + Y ω))) *
        hellingerSq P Q) := by sorry

end StatComplexityDM.LowerBound
