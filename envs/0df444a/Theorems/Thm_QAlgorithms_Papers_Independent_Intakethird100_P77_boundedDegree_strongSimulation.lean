-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_boundedDegree_strongSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.boundedDegree_strongSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:12:38.300335+00:00
-- url     : https://prove2.me/theorems/72f83eed-fbbd-4233-895f-6f7c17549d0c
-- title:
--   Strong simulation for fixed-degree observables in product-operator CAR representations
-- statement:
--   Fix a degree bound $d$ independently of the instance. For each effectively described circuit instance $s$, select an existing output wire $k_s$. Supply Hermitian CAR generators as products of one-qubit operators, a product of normalized one-qubit input states, and a list of real antisymmetric quadratic Gaussian coefficients. Supply a canonical ordered square-free polynomial $P_s$ representing $Z_{k_s}$ with degree at most $d$. Structure, the selected wire, generator factors, gate coefficients, input amplitudes and $P_s$ have polynomial-time finite descriptions to requested precision. A single deterministic polynomial-time machine, selected before $s$, precision $m$ and outcome $b$, approximates the selected one-wire probability to error $2^{-m}$.
--
--   For each length-$r$ word in $P_s$, with $U_s$ the circuit and $R_s$ its Heisenberg rotation,
--
--   $$U_s^\dagger c_{i_1}\cdots c_{i_r}U_s=\sum_{j_1,\ldots,j_r}\left(\prod_{a=1}^r(R_s)_{i_a j_a}\right)c_{j_1}\cdots c_{j_r},\qquad \#\text{tuples}=(2n_s)^r\le(2n_s)^d.$$
--
--   The expansion includes repeated indices and the empty word. The supplied polynomial has at most $\sum_{r=0}^d\binom{2n_s}{r}$ terms. This is a per-monomial count; runtime also charges circuit size, descriptions and precision. Other output wires need no bounded-degree or effective polynomial representation.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 10, Theorem 4: bounded-degree observable simulation for product-operator CAR representations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10 Theorem 4: fixed-degree observables on product-operator CAR
representations, for the selected measured wire only. Other Z observables
need not have bounded degree. The tuple bound is per monomial. The total runtime also
includes circuit length, all representation/coefficient descriptions, and m.
The canonical polynomial may have up to the displayed sum of binomial counts. -/
theorem boundedDegree_strongSimulation (d : ℕ) (F : GaussianFamily)
    (I : ProductInputs F.width) (hF : F.Effective)
    (hI : EffectiveNumbers I.data)
    (hdegree : ∀ s, (F.observable s).DegreeLE d) :
    SelectedStrongSimulation (fun s b =>
      singleWireProbability (gaussianCircuit (F.system s).majorana (F.gates s))
        (prodState (I.factor s)) (F.measured s) b) ∧
    (∀ s,
      (F.observable s).terms.length ≤
        ∑ r ∈ Finset.range (d + 1), Nat.choose (2 * F.width s) r) ∧
    (∀ s t, t ∈ (F.observable s).terms →
      Fintype.card (Fin t.1.length → Major (F.width s)) =
        (2 * F.width s) ^ t.1.length ∧
      Fintype.card (Fin t.1.length → Major (F.width s)) ≤ (2 * F.width s) ^ d ∧
      star (gaussianCircuit (F.system s).majorana (F.gates s)) *
          majoranaWord (F.system s).majorana t.1 *
          gaussianCircuit (F.system s).majorana (F.gates s) =
        expandedWord (F.system s).majorana (circuitRotation (F.gates s)) t.1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
