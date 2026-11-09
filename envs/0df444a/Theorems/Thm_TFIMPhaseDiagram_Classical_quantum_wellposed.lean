-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_quantum_wellposed
-- name    : TFIMPhaseDiagram.Classical.quantum_wellposed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:46.063435+00:00
-- url     : https://prove2.me/theorems/42b6fd88-207c-4879-94ec-5ff4eca24c7a
-- title:
--   TFIM Gibbs normalization and published API adapter
-- statement:
--   For the symmetric real TFIM data with $n\ge1$, the Hamiltonian is Hermitian, the algebra exponential has a strictly positive real trace, and the mandated published Gibbs-family adapter agrees with the normalized exponential:
--   $$\operatorname{Tr}(e^H)\in\mathbb R_{>0},\qquad \operatorname{gibbs}(H,-1,1)=e^H/\operatorname{Tr}(e^H).$$
--   This setup fact connects the reused functional-calculus API to the actual matrix exponential in the source. It is a supporting theorem, not a milestone and not an assumed structure field.
--
--   Differences from the source:
--   - encoding: the Hermitian TFIM Gibbs state exp(+H)/Tr(exp(+H)) → explicit positivity and reality of the partition trace, plus the published beta=-1 one-term adapter equality; reason: This is the source setup and API bridge, not an additional hypothesis of any result.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, §3, Eq.(6), p.6; §4, Theorem 11, pp.7–8 (setup only; not a numbered milestone)

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false

namespace TFIMPhaseDiagram.Classical
/-- Section 3, Eq.(6), p.6 and Section 4, Theorem 11: well-posed exponential Gibbs data.
This also relates the mandated published beta=-1 Gibbs API to the algebra exponential. -/
theorem quantum_wellposed {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) :
  (hamiltonian J h η).IsHermitian ∧ (partition J h η).im = 0 ∧
    0 < (partition J h η).re ∧ gibbsAdapter J h η = density J h η := by sorry
end TFIMPhaseDiagram.Classical
