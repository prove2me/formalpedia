-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_Supplement_theorem_b5
-- name    : RobustPrefLearn.MTP.Supplement.theorem_b5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:14:54.154798+00:00
-- url     : https://prove2.me/theorems/5473e661-e0fc-4404-b992-6d95ee735917
-- title:
--   Appendix B.5 theorem — Borda lower bound (corrected: δ ≤ 1/2)
-- statement:
--   Let $K\ge2$ and let $P=(p_{ij})\in\Theta^P$: all entries are positive, $p_{ij}+p_{ji}=1$, and there is a strict Borda winner $i_*(P)$. Let $0<\delta\le1/2$. Every $\delta$-PAC dueling algorithm $\pi$ satisfies
--   $$\mathbb E_P^\pi[\tau]\ge\frac{\mathrm{kl}(\delta,1-\delta)}{\displaystyle\sup_{\lambda\in\Delta(\mathcal S^P)}\inf_{\substack{\widetilde P\in\Theta^P\\i_*(\widetilde P)\ne i_*(P)}}\sum_i\sum_{j>i}\lambda(\{i,j\})\mathrm{kl}(p_{ij},\widetilde p_{ij})}.$$
--   Here $\mathcal S^P$ is the collection of unordered pairs, $s_i=(K-1)^{-1}\sum_{j\ne i}p_{ij}$ is the Borda score, and $\mathrm{kl}$ is the Bernoulli divergence. A $\delta$-PAC algorithm displays pairs only, terminates almost surely and selects the Borda winner with probability at least $1-\delta$ under every comparison matrix in $\Theta^P$.
--
--   This theorem gives the pairwise-information lower bound for identifying a Borda winner. It asserts only the finite-confidence inequality, without an asymptotic companion or an additional information-positivity premise.
--
--   **Formalization Note** The printed confidence domain is corrected; a one-vote uniform-pair policy is a counterexample at $\delta=0.99$, as recorded in DISPROOF.md. The published policy and history law are reused, with a separate Borda error event. Pair weights vanish on nonpairs and the double sum counts each unordered pair once. Versions are zero-based and the information and expectation are extended nonnegative reals.
--
--   Differences from the source:
--   - correction: 0<delta<1 → 0<delta<=1/2; reason: the printed bound is false near one; the uniform-pair one-vote counterexample at K=3 is retained in DISPROOF.md
--   - reading: Borda score divides by K-1 and alternatives have a different winner → K>=2 and alternatives in the strict-winner class ThetaP; reason: these are the domain conventions of the Borda model on pp.48–49
--   - encoding: unordered pair distributions and dueling histories → published display-set policies supported on pairs, with a separate Borda-winner error predicate; reason: the zero extension to nonpair displays is never sampled, and the finite sum i<j counts each pair once
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Theorem (unnumbered, Appendix B.5, PDF 49), p. 49; source.pdf sha256 5c09534e5696bccabf34ab8a3582c3ade8e448db308c84ee4895a5961f8629f1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Supplement_Dueling

open scoped ENNReal

namespace RobustPrefLearn.MTP.Supplement

/-- Appendix B.5, p.49. Corrected domain 0 < δ ≤ 1/2; the printed
δ ∈ (0,1) is refuted by the one-vote, uniform-pair policy recorded in DISPROOF.md.
No extra positivity assumption on the information is imposed. -/
theorem theorem_b5 (K : ℕ) (hK : 2 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (P : Comparison K) (hP : P ∈ ComparisonClass K) (π : Policy K)
    (hπ : DuelingPAC δ π) :
    ENNReal.ofReal (kl δ (1 - δ)) / duelingInfo P ≤ expTau π (duelingPref P) := by sorry

end RobustPrefLearn.MTP.Supplement
