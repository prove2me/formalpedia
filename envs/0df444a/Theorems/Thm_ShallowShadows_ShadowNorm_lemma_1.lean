-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_lemma_1
-- name    : ShallowShadows.ShadowNorm.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:58.077292+00:00
-- url     : https://prove2.me/theorems/50885d43-174e-45ab-a7ca-836df7156a26
-- title:
--   Lemma 1: $\mathcal M_d(P^\lambda) = t_{\lambda,d}P^\lambda$ with $t_{\lambda,d}=\Pr(UP^\lambda U^\dagger\in\pm\mathcal Z)\in[0,1]$
-- statement:
--   Let $n = 2m$ and $d \in \{\infty, 0, 1, 2, \dots\}$. For $\lambda \in \{0,1\}^{2n}$ let
--
--   $$
--   t_{\lambda,d} := \Pr_{U\sim\mathcal U_d}\big(UP^\lambda U^\dagger \in\pm\mathcal Z\big) \in [0,1].
--   $$
--
--   Then the measurement channel $\mathcal M_d(\rho) = \mathbb E_{U\sim\mathcal U_d}\big[\sum_b \langle b|U\rho U^\dagger|b\rangle\, U^\dagger|b\rangle\langle b|U\big]$ of Eq. (2) is diagonal in the Pauli basis:
--
--   $$
--   \mathcal M_d(P^\lambda) = t_{\lambda,d}\,P^\lambda.
--   $$
--
--   The lemma turns the eigenvalues of the measurement channel into probabilities of a classical event, which can be computed by tensor networks at logarithmic depth.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Lemma 1, Eqs. (5)–(6), p. 4 (proof Appendix A, pp. 10–11)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_tCoeff

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Lemma 1, Eqs. (5)–(6),
p. 4 (proof Appendix A, pp. 10–11): for `λ ∈ {0,1}^{2n}`, `t_{λ,d} := Pr_{U∼𝒰_d}(U P^λ U† ∈ ±𝒵)`
lies in `[0, 1]` and `M_d(P^λ) = t_{λ,d} P^λ`.

Stated for every `m` (`n = 2m`) and every depth: the brickwork ensembles `𝒰_k`, `k ∈ ℕ`, and the
global Clifford ensemble `𝒰_∞`. `M_d` is the measurement channel of Eq. (2) of the ensemble
(`ClassicalShadow.Linear.measChannel`).

**Formalization Note.** Uniform Cliffords are uniform over Cliffords modulo global phase (finiteness
of the label types as instance arguments); `n` even is `n = 2m`. -/
theorem lemma_1 (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ, ∀ lam : Bits (2 * m) × Bits (2 * m),
        (0 ≤ tCoeff (brickwork m k) lam ∧ tCoeff (brickwork m k) lam ≤ 1) ∧
          measChannel (brickwork m k) (pauli lam) = (tCoeff (brickwork m k) lam : ℂ) • pauli lam) ∧
      (∀ lam : Bits (2 * m) × Bits (2 * m),
        (0 ≤ tCoeff (globalClifford (2 * m)) lam ∧ tCoeff (globalClifford (2 * m)) lam ≤ 1) ∧
          measChannel (globalClifford (2 * m)) (pauli lam) =
            (tCoeff (globalClifford (2 * m)) lam : ℂ) • pauli lam) := by sorry

end ShallowShadows.ShadowNorm
