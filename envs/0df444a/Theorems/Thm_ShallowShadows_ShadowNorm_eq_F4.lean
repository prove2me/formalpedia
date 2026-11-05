-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_eq_F4
-- name    : ShallowShadows.ShadowNorm.eq_F4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:23.399848+00:00
-- url     : https://prove2.me/theorems/881e3ffd-0ded-4c71-8e6e-739051226a21
-- title:
--   Eq. (F4): $\mathbb E[\langle0|UP^\lambda U^\dagger|0\rangle\langle0|UP^{\lambda'}U^\dagger|0\rangle]=\delta_{\lambda\lambda'}t_{\lambda,d}$
-- statement:
--   Let $n = 2m$ and $d\in\{\infty,0,1,2,\dots\}$. For all $\lambda,\lambda'\in\{0,1\}^{2n}$,
--
--   $$
--   \mathbb E_{U\sim\mathcal U_d}\big[\langle 0|UP^\lambda U^\dagger|0\rangle\langle 0|UP^{\lambda'}U^\dagger|0\rangle\big] = \delta_{\lambda,\lambda'}\,t_{\lambda,d}.
--   $$
--
--   This second-moment identity produces the locally scrambled term $\sum_\lambda \beta_\lambda^2/t_{\lambda,d}$ in the proof of Theorem 7.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
--   - encoding: ⟨0|X|0⟩ → the (0, 0) entry X 0 0, 0 the all-zero bit string; reason: same number
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Appendix F, Eq. (F4), p. 19

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_tCoeff

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Appendix F, Eq. (F4),
p. 19: `E_{U∼𝒰_d}[⟨0|U P^λ U†|0⟩ ⟨0|U P^λ' U†|0⟩] = δ_{λ,λ'} t_{λ,d}`.

Stated for every `m` (`n = 2m`), every depth (`𝒰_k`, `k ∈ ℕ`, and `𝒰_∞`) and all
`λ, λ' ∈ {0,1}^{2n}`; `⟨0|X|0⟩` is the `(0, 0)` entry. -/
theorem eq_F4 (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ, ∀ lam lam' : Bits (2 * m) × Bits (2 * m),
        ∑ i, ((brickwork m k).w.prob i : ℂ) *
            (((brickwork m k).mat i * pauli lam * star ((brickwork m k).mat i)) 0 0 *
              ((brickwork m k).mat i * pauli lam' * star ((brickwork m k).mat i)) 0 0) =
          if lam = lam' then (tCoeff (brickwork m k) lam : ℂ) else 0) ∧
      (∀ lam lam' : Bits (2 * m) × Bits (2 * m),
        ∑ i, ((globalClifford (2 * m)).w.prob i : ℂ) *
            (((globalClifford (2 * m)).mat i * pauli lam * star ((globalClifford (2 * m)).mat i)) 0 0 *
              ((globalClifford (2 * m)).mat i * pauli lam' * star ((globalClifford (2 * m)).mat i)) 0 0) =
          if lam = lam' then (tCoeff (globalClifford (2 * m)) lam : ℂ) else 0) := by sorry

end ShallowShadows.ShadowNorm
