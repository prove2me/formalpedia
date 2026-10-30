-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_canonical_purification_fixed_input
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.canonical_purification_fixed_input
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:23:33.127322+00:00
-- url     : https://prove2.me/theorems/83736157-f2f9-4e21-9395-ef1330bf107d
-- title:
--   Canonical purification preserves fixed-input divergences
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Fix a pure normalized vector $|\psi\rangle_{RA}$ and a copy $A^\prime$ of $A$. In orthonormal bases write $|\psi\rangle=\sum_{r,a}X_{ra}|r\rangle|a\rangle$. There is a state $\rho=X^*X$ on $A^\prime$, chosen independently of the channels and the Renyi order. Put $|\Gamma\rangle=\sum_a|a\rangle|a\rangle$, $\Gamma=|\Gamma\rangle\langle\Gamma|$, and $\eta=(\sqrt\rho\otimes I_A)\Gamma(\sqrt\rho\otimes I_A)$. For every finite output system $B$, every two channels $\mathcal N_1,\mathcal N_2:A\to B$, every $\alpha>0$, and both $D_\alpha$ and $\widetilde D_\alpha$,
--
--   $$
--   \mathfrak D_\alpha(\mathcal N_1(\psi)\|\mathcal N_2(\psi))=\mathfrak D_\alpha(\mathcal N_1(\eta)\|\mathcal N_2(\eta))=\mathfrak D_\alpha((\sqrt\rho\otimes I_B)\mathcal N_1(\Gamma)(\sqrt\rho\otimes I_B)\|(\sqrt\rho\otimes I_B)\mathcal N_2(\Gamma)(\sqrt\rho\otimes I_B)).
--   $$
--
--   Every channel acts only on the $A$ factor. Order one means Umegaki relative entropy. The unnormalized entangled vector is essential for $\eta$ to have trace one. This reduces fixed-input comparisons to canonical purifications.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 12, Lemma 6; corrected by Appendix A, (A.2)–(A.7)

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

/-- Lemma 6, arXiv:1408.3373v3, PDF p.12; Appendix A, PDF p.27.
SOURCE CORRECTION: printed (3.13) has the channel supremum on its left.
Changed to the fixed-input divergence in (A.2)--(A.7), which uniquely identifies
rho=X*X from psi, independently of both channels and alpha. Gamma is unnormalized. -/
theorem canonical_purification_fixed_input
    {R A : Type} [Fintype R] [Fintype A] [DecidableEq R] [DecidableEq A]
    [Nonempty R] [Nonempty A] (psi : UnitStateVector (R × A)) :
    ∃ rho : NormalizedDensity A, rho.1 = coefficientGram psi.1 ∧
      ∀ (B : Type) [Fintype B] [DecidableEq B] [Nonempty B],
        ∀ (N M : Superop A B), IsChannel N → IsChannel M →
          ∀ alpha : ℝ, 0 < alpha →
            CanonicalIdentity (sandwichedWithUmegaki alpha) psi.1 rho.1 N M ∧
            CanonicalIdentity (petzWithUmegaki alpha) psi.1 rho.1 N M := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
