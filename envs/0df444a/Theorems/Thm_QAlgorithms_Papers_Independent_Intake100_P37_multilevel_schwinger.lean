-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_multilevel_schwinger
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.multilevel_schwinger
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:04:30.333047+00:00
-- url     : https://prove2.me/theorems/083d38ad-be7a-408a-85ab-7c3db4126ec9
-- title:
--   Schwinger equivalence with r ground levels
-- statement:
--   Let $r\ge1$, $A,m\ge0$, with one excited atomic level $e$ and $r$ degenerate ground levels $g_a$. Use $r$ photon modes, one per equal real coupling $\gamma$, under the same interaction-picture dipole and rotating-wave assumptions. The physical Hilbert space is the full sector with photon count plus excited-atom count $m+A$.
--
--   The normalized $(r+1)$-level atomic occupation embedding and its photon extension are isometries. They intertwine every collective lowering operator and the Hermitian physical and oscillator Hamiltonians, and consequently the propagators:
--
--   $$
--   \Bigl(\sum_k|g_a^k\rangle\langle e^k|\Bigr)E_{\rm atoms}
--    =E_{\rm atoms}b_a^\dagger c,
--   \qquad H_{\rm physical}E=EH_{\rm osc},
--   \qquad e^{-itH_{\rm physical}}E=Ee^{-itH_{\rm osc}}.
--   $$
--
--   Here $H_{\rm osc}=\gamma\sum_a c b_a^\dagger a_a^\dagger+\mathrm{h.c.}$, with the square-root occupation factors and zero forbidden transitions. There are $r+1$ atomic oscillator modes and $r$ retained photon modes, for $2r+1$ modes in total. This is a dynamical equivalence on the symmetric atomic sector; no qudit cloning fidelity or optimality formula is added.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 4, Sec. II B, Eqs.(16)-(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4 Eqs.(16)-(17): r ground states and r photon modes. There are
r+1 ATOMIC oscillator modes, hence 2r+1 modes including the photons. The
whole symmetric atomic sector, not an assumed cloning chain, is intertwined. -/
theorem multilevel_schwinger (r A m : ℕ) (hr : 1 ≤ r) (gamma t : ℝ) :
    (physicalH r A m gamma).IsHermitian ∧ (oscH r A m gamma).IsHermitian ∧
    (QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding (r + 1) A)ᴴ * QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding (r + 1) A = 1 ∧
    (∀ a : Fin r,
      collectiveLower r A a * QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding (r + 1) A =
        QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding (r + 1) A * occupationLower r A a) ∧
    (physicalEmbedding r A m)ᴴ * physicalEmbedding r A m = 1 ∧
    physicalH r A m gamma * physicalEmbedding r A m =
      physicalEmbedding r A m * oscH r A m gamma ∧
    QAlgorithms.Papers.Independent.Claimed50.P15.propagator (physicalH r A m gamma) t * physicalEmbedding r A m =
      physicalEmbedding r A m * QAlgorithms.Papers.Independent.Claimed50.P15.propagator (oscH r A m gamma) t := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
