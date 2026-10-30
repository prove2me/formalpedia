-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_channel_mutual_information_canonical_formula
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.channel_mutual_information_canonical_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:25:11.427736+00:00
-- url     : https://prove2.me/theorems/2b924151-11bb-4508-a997-4b6a0e8582b2
-- title:
--   Canonical formula for channel Renyi mutual information
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   For a bipartite state $\omega_{RB}$, let $I_\alpha(R;B)_\omega=\inf_{\sigma_B}D_\alpha(\omega\|\omega_R\otimes\sigma_B)$ and $\widetilde I_\alpha(R;B)_\omega=\inf_{\sigma_B}\widetilde D_\alpha(\omega\|\omega_R\otimes\sigma_B)$, where all comparisons are normalized states. Channel mutual information takes the supremum of these state quantities over all input states and finite references. Fix a channel $\mathcal N:A\to B$ and a copy $R$ of $A$. With $\Gamma$ unnormalized as in Lemma 6 and $\omega(\rho)=(\mathrm{id}_R\otimes\mathcal N)((\sqrt\rho\otimes I_A)\Gamma(\sqrt\rho\otimes I_A))$,
--
--   $$
--   I_\alpha(\mathcal N)=\sup_{\rho\in\mathcal S(R)} I_\alpha(R;B)_{\omega(\rho)}\quad(0\le\alpha\le2),\qquad \widetilde I_\alpha(\mathcal N)=\sup_{\rho\in\mathcal S(R)}\widetilde I_\alpha(R;B)_{\omega(\rho)}\quad(\alpha\ge1/2).
--   $$
--
--   Order one uses the relative entropy. These formulas retain the comparison infimum inside the input optimization.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 13, Lemma 9, (3.28)–(3.29)

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

/-- Lemma 9, arXiv:1408.3373v3, PDF pp.13--14, (3.28)--(3.29).
SOURCE CORRECTION: the RHS of printed (3.29) omits the tilde.
Use sandwichedWithUmegaki MI, as required by (3.27) and the proof's sandwichedWithUmegaki DPI.
R is the fixed copy of A named in the opening sentence. -/
theorem channel_mutual_information_canonical_formula
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    (∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ 2 →
      channelRenyiMI (petzWithUmegaki alpha) N = canonicalMI (petzWithUmegaki alpha) N) ∧
    (∀ alpha : ℝ, (1/2 : ℝ) ≤ alpha →
      channelRenyiMI (sandwichedWithUmegaki alpha) N = canonicalMI (sandwichedWithUmegaki alpha) N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
