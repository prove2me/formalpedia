-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_lemma_13
-- name    : ShallowShadows.ShadowNorm.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:34.14085+00:00
-- url     : https://prove2.me/theorems/71ff1aa5-9425-4502-b544-f7ad6e30a090
-- title:
--   Lemma 13: $\mathbb E\prod_i\langle0|UP_iU^\dagger|0\rangle$ vanishes unless $\prod_iP_i=\pm\mathbb I$, and is $\Pr(\forall i,\,UP_iU^\dagger\in\pm\mathcal Z)$ if $\prod_iP_i=\mathbb I$
-- statement:
--   Let $\mathcal U$ be a Pauli invariant ensemble of Clifford unitaries and let $P_1,\dots,P_k$ be Pauli strings.
--
--   1. **(A1)** If $\prod_{i=1}^k P_i \neq \pm\mathbb I$, then
--   $$
--   \mathbb E_{U\sim\mathcal U}\Big[\prod_{i=1}^k\langle 0|UP_iU^\dagger|0\rangle\Big] = 0.
--   $$
--   2. **(A2)** If $\prod_{i=1}^k P_i = \mathbb I$, then
--   $$
--   \mathbb E_{U\sim\mathcal U}\Big[\prod_{i=1}^k\langle 0|UP_iU^\dagger|0\rangle\Big] = \Pr_{U\sim\mathcal U}\big(\forall i,\ UP_iU^\dagger\in\pm\mathcal Z\big).
--   $$
--
--   Here $|0\rangle$ is the all-zero computational basis state and the product $\prod_i P_i = P_1P_2\cdots P_k$ is the ordered matrix product. The lemma reduces every moment of Pauli expectation values under a Pauli invariant ensemble to a probability, which is how the eigenvalues of the measurement channel become the probabilities $t_{\lambda,d}$ and $\tau_{(\lambda,\lambda'),d}$.
--
--   Differences from the source:
--   - reading: a Pauli invariant ensemble U → a finite ensemble (ClassicalShadow.Linear.Primitive) with IsPauliInvariant whose positive-weight unitaries are Clifford (IsCliffordPrimitive); reason: the paper's ensembles are ensembles of Clifford gates (§III); a law on Cliffords modulo phase is a finite family of weights
--   - encoding: P_1, …, P_k ∈ P_n → labels P : Fin k → {0,1}^n × {0,1}^n, P_i = pauli (P i), product the ordered List product; reason: P_n is the set of phase-free Pauli strings P^λ
--   - encoding: ∏ P_i ≠ ±I → two hypotheses ∏ P_i ≠ 1 and ∏ P_i ≠ −1; reason: same condition
--   - encoding: ⟨0|X|0⟩ → the (0, 0) entry X 0 0, 0 the all-zero bit string; reason: same number
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Lemma 13, Eqs. (A1)–(A2), p. 10

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_prob
import Definitions.Def_ShallowShadows_ShadowNorm_InPmZ
import Definitions.Def_ShallowShadows_ShadowNorm_IsPauliInvariant
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Lemma 13, Eqs. (A1)–(A2),
p. 10. Let `𝒰` be a Pauli invariant ensemble of Clifford unitaries and `P_1, …, P_k` Pauli strings
(`P_j = P^{λ_j}`).

(A1) If `∏_{j=1}^k P_j ≠ ±𝕀`, then `E_{U∼𝒰}[∏_j ⟨0|U P_j U†|0⟩] = 0`.

(A2) If `∏_{j=1}^k P_j = 𝕀`, then `E_{U∼𝒰}[∏_j ⟨0|U P_j U†|0⟩] = Pr_{U∼𝒰}(∀ j, U P_j U† ∈ ±𝒵)`.

**Formalization Note.** The product `∏ P_j` is the ordered matrix product `P_1 ⋯ P_k`;
`⟨0|X|0⟩` is the `(0, 0)` entry, `0` the all-zero bit string. "Pauli invariant ensemble" is a
finite ensemble with `IsPauliInvariant` whose positive-weight unitaries are Clifford
(`IsCliffordPrimitive`, the paper's standing assumption that ensembles consist of Cliffords). -/
theorem lemma_13 {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (hPI : IsPauliInvariant E)
    (hCl : IsCliffordPrimitive E) (k : ℕ) (P : Fin k → Bits n × Bits n) :
    ((List.ofFn fun j => pauli (P j)).prod ≠ 1 → (List.ofFn fun j => pauli (P j)).prod ≠ -1 →
        ∑ i, (E.w.prob i : ℂ) * ∏ j, (E.mat i * pauli (P j) * star (E.mat i)) 0 0 = 0) ∧
      ((List.ofFn fun j => pauli (P j)).prod = 1 →
        ∑ i, (E.w.prob i : ℂ) * ∏ j, (E.mat i * pauli (P j) * star (E.mat i)) 0 0 =
          (prob E (fun U => ∀ j, InPmZ ((U : Op n) * pauli (P j) * star (U : Op n))) : ℂ)) := by sorry

end ShallowShadows.ShadowNorm
