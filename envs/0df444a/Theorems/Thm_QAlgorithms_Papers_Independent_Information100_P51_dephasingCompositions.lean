-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P51_dephasingCompositions
-- name    : QAlgorithms.Papers.Independent.Information100.P51.dephasingCompositions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:50:31.732916+00:00
-- url     : https://prove2.me/theorems/cff8cc53-6e63-439a-84d9-cf97351ea567
-- title:
--   Fock dephasing absorbs bosonic dephasing on either side
-- statement:
--   Let $p$ be a nonnegative Lebesgue probability density on $[-\pi,\pi]$, and let $\mathcal N_\mu$ be the single-mode bosonic dephasing channel with Fock coefficients
--
--   $$
--   (\mathcal N_\mu[X])_{k\ell}=X_{k\ell}\int_{-\pi}^{\pi}p(\phi)e^{-i\phi(k-\ell)}\,d\phi,\qquad k,\ell\in\mathbb N.
--   $$
--
--   Identify its input and output Fock spaces. Let $\Delta_A$, $\Delta_B$, and $\Delta$ denote complete dephasing in the paired Fock bases, with their respective input and output systems. Then, as maps on all trace-class operators,
--
--   $$
--   \Delta_B\circ\mathcal N_\mu=\mathcal N_\mu\circ\Delta_A=\Delta.
--   $$
--
--   This identity identifies a common completely dephased comparison channel. It requires no normalization, positivity, or energy bound on the input operator.
--
--   **Formalization Note** The operator maps are represented by their complete Fock coefficient arrays. Their domain is the subtype of trace-class arrays, characterized by summable nuclear rank-one expansions.
-- source:
--   No advantage from classical assistance for energy-constrained bosonic dephasing channels, arXiv:2610.13854v1, PDF p. 6, Lemma 2.2, Eq. (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P51

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P51

/-- Lemma 2.2, arXiv:2610.13854v1, PDF p.6, Eq.(23).
Both compositions equal complete dephasing on every trace-class input. Equality of all
Fock coefficients is equality of the underlying operators; no input state or energy
hypothesis is imposed. Identification of A and B makes Delta_A, Delta_B and Delta the same
coordinate map. -/
theorem dephasingCompositions (mu : PhaseDensity) :
    (fun X : FockTraceClass => fockDephasing (bosonicDephasing mu X.val)) =
      (fun X : FockTraceClass => fockDephasing X.val) ∧
    (fun X : FockTraceClass => bosonicDephasing mu (fockDephasing X.val)) =
      (fun X : FockTraceClass => fockDephasing X.val) := by sorry

end QAlgorithms.Papers.Independent.Information100.P51

end
