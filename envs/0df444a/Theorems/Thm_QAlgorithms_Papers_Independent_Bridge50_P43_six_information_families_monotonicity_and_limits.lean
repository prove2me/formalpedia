-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_six_information_families_monotonicity_and_limits
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.six_information_families_monotonicity_and_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:25:59.571239+00:00
-- url     : https://prove2.me/theorems/1dbc76fa-9c3f-4e20-b062-5d38f08c74e2
-- title:
--   Monotonicity and order-one limits of six information families
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   For every pair of channels $\mathcal N_1,\mathcal N_2$, every bipartite state $\rho_{RB}$, and every channel $\mathcal N$, each Petz information family is monotone nondecreasing on its nonnegative order domain, and each sandwiched family is monotone nondecreasing for positive orders. The state mutual informations minimize divergence from $\rho_R\otimes\sigma_B$ over normalized $\sigma_B$; channel mutual informations then maximize over all mixed inputs and finite references. Moreover,
--
--   $$
--   \begin{aligned}
--   \lim_{\alpha\to1}D_\alpha(\mathcal N_1\|\mathcal N_2)&=\lim_{\alpha\to1}\widetilde D_\alpha(\mathcal N_1\|\mathcal N_2)=D(\mathcal N_1\|\mathcal N_2),\\
--   \lim_{\alpha\to1}I_\alpha(R;B)_\rho&=\lim_{\alpha\to1}\widetilde I_\alpha(R;B)_\rho=D(\rho_{RB}\|\rho_R\otimes\rho_B),\\
--   \lim_{\alpha\to1}I_\alpha(\mathcal N)&=\lim_{\alpha\to1}\widetilde I_\alpha(\mathcal N)=I(\mathcal N).
--   \end{aligned}
--   $$
--
--   Limits are two-sided within the order domain with order one deleted; the values at one use Umegaki. Infinite channel divergence is retained. This supplies the order-one transition for all six families.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 14, Lemma 10, (3.30)–(3.32)

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

/-- Lemma 10, arXiv:1408.3373v3, PDF p.14; Appendix A, PDF pp.28--30.
All three clauses and both families occur explicitly. Extended limits preserve infinite D.
Petz has order-zero support-projector convention; sandwichedWithUmegaki orders are strictly positive. -/
theorem six_information_families_monotonicity_and_limits :
    (∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
        [Nonempty A] [Nonempty B],
      ∀ (N M : Superop A B), IsChannel N → IsChannel M →
        OrderOneProperties (fun alpha => channelDiv (petzWithUmegaki alpha) N M) (Set.Ici 0)
          (channelDiv relativeD N M) ∧
        OrderOneProperties (fun alpha => channelDiv (sandwichedWithUmegaki alpha) N M) (Set.Ioi 0)
          (channelDiv relativeD N M)) ∧
    (∀ (R B : Type) [Fintype R] [Fintype B] [DecidableEq R] [DecidableEq B]
        [Nonempty R] [Nonempty B], ∀ rho : NormalizedDensity (R × B),
        OrderOneProperties (fun alpha => stateRenyiMI (petzWithUmegaki alpha) rho.1) (Set.Ici 0)
          (stateMI rho.1) ∧
        OrderOneProperties (fun alpha => stateRenyiMI (sandwichedWithUmegaki alpha) rho.1) (Set.Ioi 0)
          (stateMI rho.1)) ∧
    (∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
        [Nonempty A] [Nonempty B], ∀ (N : Superop A B), IsChannel N →
        OrderOneProperties (fun alpha => channelRenyiMI (petzWithUmegaki alpha) N) (Set.Ici 0)
          (stabilizedMutualInformation N) ∧
        OrderOneProperties (fun alpha => channelRenyiMI (sandwichedWithUmegaki alpha) N) (Set.Ioi 0)
          (stabilizedMutualInformation N)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
