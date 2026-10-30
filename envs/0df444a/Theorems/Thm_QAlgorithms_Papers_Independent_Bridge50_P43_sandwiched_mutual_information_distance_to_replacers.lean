-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_sandwiched_mutual_information_distance_to_replacers
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.sandwiched_mutual_information_distance_to_replacers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:26:39.058553+00:00
-- url     : https://prove2.me/theorems/bd413c90-80de-497c-a284-a70535d32a6b
-- title:
--   Channel mutual information as distance to replacers
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   For a channel $\mathcal N:A\to B$ and a finite real order $\alpha\ge1/2$, define $\widetilde I_\alpha(\mathcal N)$ as the supremum over all finite-reference inputs of the infimum of sandwiched divergence from $\psi_R\otimes\sigma_B$. Then
--
--   $$
--   \widetilde I_\alpha(\mathcal N)=\inf_{\sigma_B\in\mathcal S(B)}\widetilde D_\alpha(\mathcal N\|\mathcal R_{\sigma_B}),\qquad \mathcal R_{\sigma_B}(X)=\operatorname{Tr}(X)\sigma_B.
--   $$
--
--   The channel divergence on the right maximizes over all finite-reference mixed inputs. All comparison states, including singular ones, are allowed; order one uses Umegaki. The identity exchanges the input supremum and comparison infimum.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 14, Lemma 11, (3.33)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P43

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence relativeD petzD sandwichedD)

open QAlgorithms.Papers.Independent.Information100.P71
  (SupportIncluded supportPower AdaptiveTest adaptiveInput adaptiveAccept adaptiveBeta channelPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)
-- Exactly the trace-preparation map of PDF pp.5--6, on every operator.

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

/-- Lemma 11, arXiv:1408.3373v3, PDF p.14; Appendix A, PDF pp.30--31, (3.33).
The comparison infimum is moved outside the input supremum as a theorem.
All density operators, including singular ones and alpha=1, remain admissible. -/
theorem sandwiched_mutual_information_distance_to_replacers
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (alpha : ℝ) (ha : (1/2 : ℝ) ≤ alpha) :
    channelRenyiMI (sandwichedWithUmegaki alpha) N =
      ⨅ sigma : NormalizedDensity B, channelDiv (sandwichedWithUmegaki alpha) N (replacer sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
