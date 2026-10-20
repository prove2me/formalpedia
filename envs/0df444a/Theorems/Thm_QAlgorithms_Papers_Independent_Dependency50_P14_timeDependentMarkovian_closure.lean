-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P14_timeDependentMarkovian_closure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P14.timeDependentMarkovian_closure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:44:39.263335+00:00
-- url     : https://prove2.me/theorems/873c2d59-57ea-4428-87d4-fcb3843ff898
-- title:
--   Closure of time-dependent Markovian channels and its GKLS wedge
-- statement:
--   Let $N\ge1$, let $P_{\mathrm{cp}}^0$ be the identity component of invertible CPTP maps on $\mathrm{her}(N)$, and let $\mathcal T=\overline{\langle\exp(\mathcal L(P_{\mathrm{cp}}^0))\rangle_S}$. Write $M_{\mathrm{td}}$ for the endpoints at finite nonnegative times of piecewise-continuous GKLS master equations $\dot X(t)=A(t)X(t)$, starting at $X(0)=I$. The generators have the forward form
--
--   $$
--   A(\rho)=-i[H,\rho]+\sum_{j=1}^{r}\left(V_j\rho V_j^\dagger-\tfrac12(V_j^\dagger V_j\rho+\rho V_j^\dagger V_j)\right),
--   $$
--
--   where $H=H^\dagger$ and the finitely many $V_j$ are arbitrary complex matrices. Denote their set by $W_{\mathrm{GKLS}}$. Then, with closures relative to invertible maps,
--
--   $$
--   \overline{M_{\mathrm{td}}}=\mathcal T,\qquad
--   \mathcal T\text{ is a Lie subsemigroup},\qquad
--   \mathcal L(\mathcal T)=\mathcal L(P_{\mathrm{cp}}^0)=W_{\mathrm{GKLS}}.
--   $$
--
--   The one-sided curve tangent cone is meant by the source's phrase “tangent space”. This gives a geometric characterization of the closure of Markovian endpoints; it does not require a finite-time GKLS trajectory for every limit endpoint.
-- source:
--   Lie-Semigroup Structures for Reachability and Control of Open Quantum Systems, arXiv:0811.3906v4, PDF p. 8, Corollary III.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P14

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P14

open QAlgorithms.Papers.Independent.Information100.P59 (Operator dissipator)

/-- arXiv:0811.3906v4 PDF p.8, Corollary III.1: closure of ordinary Markovian
endpoints, Lie-subsemigroup structure, and the forward GKLS tangent wedge.
The source's 'tangent space' means its one-sided cone, not a vector subspace. -/
theorem timeDependentMarkovian_closure {N : ℕ} (hN : 0 < N) :
    closure (timeDependentMarkovian N) = markovSemigroup N ∧
    IsLieSubsemigroup (markovSemigroup N) ∧
    tangent (markovSemigroup N) = tangent (channelComponent N) ∧
    tangent (markovSemigroup N) = gklsGenerators N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P14

end
