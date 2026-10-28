-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_entropy_triple_counterexample
-- name    : QAlgorithms.Papers.Independent.Support50.P42.entropy_triple_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:25:30.636875+00:00
-- url     : https://prove2.me/theorems/9cfff6db-cfea-4b77-9305-d8624475f9ad
-- title:
--   Equal entropy triples with different mixed-state entanglement
-- statement:
--   Write $C=(|00\rangle\langle00|+|11\rangle\langle11|)/2$. On two spins per observer define $\rho=C\otimes C$ and $\sigma=|\Psi^-\rangle\langle\Psi^-|\otimes I_4/4$, regrouping Alice's two spins against Bob's two spins. Both are normalized density matrices and satisfy
--
--   $$S(\rho_A)=S(\rho_B)=S(\rho)=S(\sigma_A)=S(\sigma_B)=S(\sigma)=2.$$
--
--   The state $\rho$ is separable, whereas $\sigma$ is entangled; discarding the second spin locally on both sides of $\sigma$ leaves exactly a singlet. Thus the subsystem and total entropy triple does not determine mixed-state entanglement. The uncorrelated second pair is explicitly maximally mixed.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 16, §V: equal subsystem/total entropies with different mixed-state entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.16: two four-spin mixed states with all three entropies equal to two.
The second uncorrelated pair is maximally mixed. The first state is separable;
the second is entangled and yields a singlet upon local disposal. -/
theorem entropy_triple_counterexample :
    let rho := twoPairs classicalPair classicalPair
    let sigma := twoPairs Dependency50.P42.singletState ((1/4 : ℂ) • 1)
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    vnEntropy rho=2 ∧ vnEntropy (traceLeft rho)=2 ∧ vnEntropy (traceRight rho)=2 ∧
    vnEntropy sigma=2 ∧ vnEntropy (traceLeft sigma)=2 ∧ vnEntropy (traceRight sigma)=2 ∧
    Entanglement.IsSeparablePositive rho ∧ ¬Entanglement.IsSeparablePositive sigma ∧
    discardSecond sigma=Dependency50.P42.singletState := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
