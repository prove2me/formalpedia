-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_channel_divergence_fixed_copy_reductions
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.channel_divergence_fixed_copy_reductions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:24:18.730325+00:00
-- url     : https://prove2.me/theorems/330a5d96-2882-477a-9a3e-316cf6ee52f2
-- title:
--   Fixed-copy pure and canonical channel divergence formulas
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   For channels $\mathcal N_1,\mathcal N_2:A\to B$, define $\mathfrak D(\mathcal N_1\|\mathcal N_2)$ by taking the supremum of $\mathfrak D(\mathcal N_1(\psi)\|\mathcal N_2(\psi))$ over all mixed inputs and all finite references. If $\mathfrak D=\widetilde D_\alpha$ with $\alpha\ge1/2$, or $\mathfrak D=D_\alpha$ with $0\le\alpha\le2$, then
--
--   $$
--   \mathfrak D(\mathcal N_1\|\mathcal N_2)=\sup_{|\psi\rangle_{A^\prime A}}\mathfrak D(\mathcal N_1(\psi)\|\mathcal N_2(\psi))=\sup_{\rho\in\mathcal S(A^\prime)}\mathfrak D((\sqrt\rho\otimes I_B)\mathcal N_1(\Gamma)(\sqrt\rho\otimes I_B)\|(\sqrt\rho\otimes I_B)\mathcal N_2(\Gamma)(\sqrt\rho\otimes I_B)).
--   $$
--
--   Here $A^\prime$ is a fixed copy of $A$, pure vectors are normalized, and $\Gamma=|\Gamma\rangle\langle\Gamma|$ for the unnormalized vector $|\Gamma\rangle=\sum_a|a\rangle|a\rangle$. At order one use Umegaki; at Petz order zero use the support projector. These are reductions of the original stabilized optimizations.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 12, Lemma 7, (3.15)–(3.17)

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

/-- Lemma 7, arXiv:1408.3373v3, PDF p.12, (3.15)--(3.17).
All-ancilla optimization is the definition; the pure and canonical reductions are conclusions. -/
theorem channel_divergence_fixed_copy_reductions
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N M : Superop A B) (hN : IsChannel N) (hM : IsChannel M) :
    (∀ alpha : ℝ, (1/2 : ℝ) ≤ alpha →
      channelDiv (sandwichedWithUmegaki alpha) N M = fixedPureDiv (sandwichedWithUmegaki alpha) N M ∧
      fixedPureDiv (sandwichedWithUmegaki alpha) N M = canonicalDiv (sandwichedWithUmegaki alpha) N M) ∧
    (∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ 2 →
      channelDiv (petzWithUmegaki alpha) N M = fixedPureDiv (petzWithUmegaki alpha) N M ∧
      fixedPureDiv (petzWithUmegaki alpha) N M = canonicalDiv (petzWithUmegaki alpha) N M) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
