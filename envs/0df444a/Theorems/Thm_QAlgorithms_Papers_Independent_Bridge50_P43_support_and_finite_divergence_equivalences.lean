-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P43_support_and_finite_divergence_equivalences
-- name    : QAlgorithms.Papers.Independent.Bridge50.P43.support_and_finite_divergence_equivalences
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:27:23.002298+00:00
-- url     : https://prove2.me/theorems/1b0c0da7-3d6d-4a86-879f-3ef37f223549
-- title:
--   Equivalent support and finite-divergence conditions
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces. States are positive operators of trace one, channels are completely positive and trace preserving, and logarithms are base two. Extended entropies retain $+\infty$.
--
--   Fix a channel $\mathcal N:A\to B$ and a state $\sigma_B$. The following four conditions are equivalent:
--
--   1. For every integer $k\ge0$, every finite reference $R$, and every state $\psi_{RA^k}$,
--
--   $$
--   \operatorname{supp}((\mathrm{id}_R\otimes\mathcal N^{\otimes k})(\psi))\subseteq\operatorname{supp}(\psi_R\otimes\sigma_B^{\otimes k}).
--   $$
--
--   2. Every state $\rho_A$ satisfies $\operatorname{supp}\mathcal N(\rho_A)\subseteq\operatorname{supp}\sigma_B$.
--
--   3. $\widetilde D_\alpha(\mathcal N\|\mathcal R_{\sigma_B})<+\infty$ for every finite real $\alpha\ge1$.
--
--   4. The same finiteness holds for some finite real $\alpha\ge1$.
--
--   At $k=0$ the tensor-power state is the tensor unit and both operators reduce to $\psi_R$. Order one uses Umegaki. The equivalence identifies exactly when finite-information arguments apply without imposing full rank on $\sigma_B$.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, PDF p. 17, Lemma 12

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

/-- Lemma 12, arXiv:1408.3373v3, PDF pp.17--18.
All four conditions are equivalent. k=0 is explicitly included with the tensor unit;
orders are finite real numbers, with Umegaki at order one. -/
theorem support_and_finite_divergence_equivalences
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (sigma : NormalizedDensity B) :
    let blockSupport := ∀ k d : ℕ, 0 < d → ∀ psi : NormalizedDensity (Fin d × (Fin k → A)),
      SupportIncluded (idTensorSuperop (channelPower N k) psi.1)
        (Matrix.kronecker (traceRight psi.1) (tensorDensity sigma.1 k))
    let singleSupport := ∀ rho : NormalizedDensity A, SupportIncluded (N rho.1) sigma.1
    let allFinite := ∀ alpha : ℝ, 1 ≤ alpha →
      channelDiv (sandwichedWithUmegaki alpha) N (replacer sigma.1) < ⊤
    let someFinite := ∃ alpha : ℝ, 1 ≤ alpha ∧
      channelDiv (sandwichedWithUmegaki alpha) N (replacer sigma.1) < ⊤
    (blockSupport ↔ singleSupport) ∧ (singleSupport ↔ allFinite) ∧
      (allFinite ↔ someFinite) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P43

end
