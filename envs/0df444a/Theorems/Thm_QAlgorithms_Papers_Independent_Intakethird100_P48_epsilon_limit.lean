-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_epsilon_limit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.epsilon_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:31:40.104476+00:00
-- url     : https://prove2.me/theorems/2588486e-757c-4074-8d69-3050ba2281a9
-- title:
--   Exact amplification, limit three, and a Tsirelson crossing
-- statement:
--   Let $0<\varepsilon<1/2$ and let $P_\varepsilon$ have perfectly correlated uniform outputs except at input $11$, where each unequal-output pair has probability $\varepsilon/2$. Write $P_\varepsilon^{(n)}=\operatorname{NDP}_n(P_\varepsilon)$ for the local-XOR output from $n$ independent identical copies, and let $\operatorname{NL}$ denote the full absolute CHSH maximum. Then
--
--   $$
--   \operatorname{NL}(P_\varepsilon^{(n)})=3-(1-2\varepsilon)^n\quad(n\ge1),\qquad
--   \lim_{n\to\infty}\operatorname{NL}(P_\varepsilon^{(n)})=3.
--   $$
--
--   The entire behavior $P_\varepsilon$ has no quantum realization. Moreover, if $\varepsilon\le\sqrt2-1$, then
--
--   $$
--   \operatorname{NL}(P_\varepsilon)\le2\sqrt2,
--   \qquad \exists n>1:\ \operatorname{NL}(P_\varepsilon^{(n)})>2\sqrt2.
--   $$
--
--   Thus resources at or below the Tsirelson CHSH value can amplify past it while remaining post-quantum resources. The limit statement makes no claim of attaining $3$ with finitely many copies.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 3, Unnumbered: exact amplification, limit 3, and post-quantum resources

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.3, consequence of Theorem 1: exact amplification and limit 3,
non-quantum realizability, and crossing Tsirelson from the printed resource interval.
No finite-copy attainment of 3 is asserted. -/
theorem epsilon_limit (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2) :
    (∀ n : ℕ, 0 < n →
      nonlocality (parallelOutputLaw (parityProtocol n) (epsilonBox epsilon)) =
        3 - (1 - 2 * epsilon) ^ n) ∧
    Filter.Tendsto
      (fun n : ℕ => nonlocality (parallelOutputLaw (parityProtocol n) (epsilonBox epsilon)))
      Filter.atTop (nhds 3) ∧
    ¬ IsQuantum (epsilonBox epsilon) ∧
    (epsilon ≤ Real.sqrt 2 - 1 →
      nonlocality (epsilonBox epsilon) ≤ 2 * Real.sqrt 2 ∧
      ∃ n : ℕ, 1 < n ∧
        2 * Real.sqrt 2 < nonlocality (parallelOutputLaw (parityProtocol n) (epsilonBox epsilon))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
