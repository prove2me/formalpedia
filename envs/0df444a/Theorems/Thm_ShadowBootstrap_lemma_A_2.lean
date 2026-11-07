-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_A_2
-- name    : ShadowBootstrap.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:09.387876+00:00
-- url     : https://prove2.me/theorems/1a5df9c1-4ce7-464f-b4df-d68591ad6272
-- title:
--   Lemma A.2 — the suffix ensembles $E_\ell$ satisfy Eq. (8) with a universal constant and have depth $O(\log n)$
-- statement:
--   Let $k := \max\{8, 2\lceil\log_2 n\rceil\}$ and, for $\ell = 0, \dots, n-1$, $n - \ell = mk + r$ with $0 \le r \le k-1$, $E_\ell := E_{2L}(km) \otimes \mathrm{Cl}(r)$ with shadow channel $\mathcal M_\ell$. There are constants $C$ and $D$, independent of $n$ and $\ell$, such that for every $n$ and $\ell$:
--
--   1. $E_\ell$ is a Clifford ensemble and $\mathcal M_\ell$ is invertible;
--   2. for every $(n-\ell)$-qubit state $\rho$ and Hermitian $O$,
--   $$\mathrm{Var}\big[\operatorname{Tr}(O\hat\rho)\big] \le C\|O\|_F^2,\qquad \hat\rho := \mathcal M_\ell^{-1}(U^\dagger|z\rangle\langle z|U),\ U \sim E_\ell;$$
--   3. every unitary of $E_\ell$ is, up to a global phase, the unitary of a circuit over $\{H, S, CX\}$ of depth at most $D(\lfloor\log_2 n\rfloor + 1)$.
--
--   These are the measurement ensembles of the initialization (Lemma 5.4) and, for $\ell = 0$, of the bootstrapping stages.
--
--   Differences from the source:
--   - generalization: the variance bound of Lemma A.2 → also: Clifford ensemble, invertible M_ℓ, and circuits of depth O(log n) realizing every unitary; reason: Lemma 5.4 states these properties of the same ensembles and A.2's proof establishes them ('the component channels are invertible', 'the total depth is O(k) = O(log(n))')
--   - reading: depth O(log n) → valid circuits over {H, S, CX} (layers of gates on disjoint qubits) of depth ≤ D(⌊log₂ n⌋ + 1), equal to the unitary up to a global phase; reason: the gate set of §3.1 and Lemma 6.1; +1 because n = 1 needs depth ≥ 1
--   - encoding: ℓ = 0, …, n − 1 → the suffix size j = n − ℓ ∈ {1, …, n}; reason: the same ensembles
--   - encoding: factors on zero qubits are omitted → a one-label factor whose unitary is a global phase; reason: it changes no probability, channel or shadow
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma A.2, p.34, its proof, pp.34–35, and Lemma 5.4, p.17

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_Circuit
import Definitions.Def_ShadowBootstrap_suffixEnsemble
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma A.2, p.34 (shallow ensembles for all suffix sizes), with the depth clause of Lemma 5.4
(p.17) and of A.2's proof (p.35): let `k := max{8, 2⌈log₂ n⌉}` and, for `ℓ = 0, …, n−1`,
`E_ℓ := E2L(km) ⊗ Cl(r)` with `n − ℓ = mk + r`. For every `(n−ℓ)`-qubit state `ρ` and Hermitian
`O`, `Var[Tr(Oρ̂)] ≤ C_ℓ‖O‖_F²` with `C_ℓ = O(1)`, where `ρ̂ := M_ℓ⁻¹(U†|z⟩⟨z|U)`, `U ∼ E_ℓ`.

**Formalization Note** The ensemble is indexed by the suffix size `j = n − ℓ ∈ {1, …, n}`. One
constant `C` serves every `n` and `ℓ`. Besides the printed variance bound, the statement asserts
what Lemma 5.4 and the proof of A.2 state about the same ensemble: it is a Clifford ensemble, its
shadow channel `M_ℓ` is invertible ("the component channels are invertible"), and every unitary in
it is, up to a global phase, the unitary of a valid circuit over `{H, S, CX}` of depth
`O(log n)`, read as `≤ D(⌊log₂ n⌋ + 1)` (`n = 1` needs depth `≥ 1`). -/
theorem lemma_A_2 :
    ∃ C D : ℝ, ∀ [∀ k, Fintype (CliffordLabel k)] (n j : ℕ), 1 ≤ j → j ≤ n →
      IsCliffordPrimitive (suffixEnsemble n j) ∧
      IsUnit (measChannel (suffixEnsemble n j)) ∧
      (∀ ρ : Op j, WildeQIT.IsDensityOperator ρ → ∀ O : Op j, O.IsHermitian →
        snapVar (suffixEnsemble n j) ρ O ≤ C * frobSq O) ∧
      ∃ circ : SuffixLabel n j → Circuit j, ∀ lab : SuffixLabel n j,
        Circuit.IsValid (circ lab) ∧ (depth (circ lab) : ℝ) ≤ D * (Nat.log 2 n + 1) ∧
        ∃ c : ℂ, ‖c‖ = 1 ∧ circUnitary (circ lab) = c • (suffixEnsemble n j).mat lab := by sorry

end ShadowBootstrap
