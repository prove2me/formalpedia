-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_jordanWigner_strongSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.jordanWigner_strongSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:13:15.397032+00:00
-- url     : https://prove2.me/theorems/4a73b19f-34fe-40ef-aeba-ab760bf2e17b
-- title:
--   Strong simulation of global Jordan–Wigner Gaussian circuits
-- statement:
--   Use the Jordan–Wigner generators $c_{2k-1}=Z_1\cdots Z_{k-1}X_k$ and $c_{2k}=Z_1\cdots Z_{k-1}Y_k$. Let a uniformly described polynomial-size circuit consist of arbitrary Gaussian gates $e^{iH}$, where $H=i\sum_{\mu\ne\nu}h_{\mu\nu}c_\mu c_\nu$ and $h$ is real antisymmetric. Let the input be any product of normalized one-qubit states. All quadratic coefficients and input amplitudes are given by effective polynomial-time bit descriptions. There is one deterministic polynomial-time simulator, selected before the input, wire $k$, outcome $b$, and precision $m$, whose dyadic output satisfies
--
--   $$|q-p_b|\le2^{-m}.$$
--
--   Gate descriptions, circuit size, and requested precision are charged. These gates may act globally; no locality restriction or Gaussian/parity restriction on the product input is added. The result relies on the bounded-degree observable $Z_k=-ic_{2k-1}c_{2k}$.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 10, Section 5: arbitrary Jordan–Wigner Gaussian circuits are strongly simulatable

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10--11 unnumbered Gaussian simulation result. Product inputs need
not be Gaussian and need not have definite fermionic parity. -/
theorem jordanWigner_strongSimulation (F : JWFamily) (I : ProductInputs F.width)
    (hF : F.Effective) (hI : EffectiveNumbers I.data) :
    StrongSimulation F.width (fun s k b =>
      singleWireProbability (gaussianCircuit (jordanWigner (F.width s)) (F.gates s))
        (prodState (I.factor s)) k b) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
