-- Prove2me | Theorems.Thm_QuantumPRC_lemma_3_8
-- name    : QuantumPRC.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:55.83904+00:00
-- url     : https://prove2.me/theorems/654b1dfc-7fd7-46da-89c5-131cf5c58ca0
-- title:
--   Lemma 3.8 — the Pauli twirl of a $t$-local channel is a mixture of Pauli errors of weight $\le t$
-- statement:
--   Let $t,m$ be integers and let $\mathcal E$ be a CPTP map on $m$ qubits with a Kraus representation $\mathcal E(\cdot)=\sum_iE_i(\cdot)E_i^\dagger$ such that $\mathrm{wt}(E_i)\le t$ for all $i$. Define the twirled channel $\mathcal E^{\mathrm{tw}}:=\mathbb E_{P\leftarrow\mathcal P_m}\,P^\dagger\circ\mathcal E\circ P$, i.e. $\mathcal E^{\mathrm{tw}}(\rho)=\frac1{|\mathcal P_m|}\sum_{P\in\mathcal P_m}P^\dagger\,\mathcal E(P\rho P^\dagger)\,P$. Then there is a probability distribution $\{p_Q\}_{Q\in\mathcal P_m}$ such that, for every operator $\rho$,
--
--   $$
--   \mathcal E^{\mathrm{tw}}(\rho)=\sum_{Q\in\mathcal P_m:\ \mathrm{wt}(Q)\le t}p_Q\,Q\rho Q^\dagger .
--   $$
--
--   Averaging over the random Pauli in the PRIC key turns arbitrary local noise into a mixture of fixed low-weight Pauli errors (Eq. (124)).
--
--   Differences from the source: none.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 3.8, p.18 (proof pp.79–81)

import Mathlib
import Definitions.Def_QuantumPRC_IsLocalNoise

open Matrix

namespace QuantumPRC

/-- **Lemma 3.8** (Pauli twirl of a local channel). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Lemma 3.8, p.18 (proof pp.79–81): "Let `t, m` be integers. Given a CPTP map `E` from `m`
qubits to `m` qubits, define the CPTP map `E_tw` from `m` qubits to `m` qubits by
`E_tw := 𝔼_{P←P_m} P† ∘ E ∘ P`. If `E` has a Kraus representation `E(·) = Σ_i E_i(·)E_i†` with `wt(E_i) ≤ t`
for all `i`, then there exists a probability distribution `{p_Q}_Q` such that
`E_tw(·) = Σ_{Q∈P_m : wt(Q)≤t} p_Q Q(·)Q†`."

**Formalization Note.** `P_m` is indexed by `PauliIdx m` (phase `i^k`, strings `x, z`; `4^{m+1}`
elements, uniform average); `P† ∘ E ∘ P` is `ρ ↦ P† E(PρP†) P`; `wt(Q)` for `Q = i^k X^x Z^z` is
`pauliWeight x z`; the identity holds for every operator `ρ`. -/
theorem lemma_3_8 (t m : ℕ) (E : WildeQIT.QChannel (Bits m) (Bits m))
    (hE : ∀ i, pauliWt (E.K i) ≤ t) :
    ∃ p : PauliIdx m → ℝ, (∀ Q, 0 ≤ p Q) ∧ ∑ Q, p Q = 1 ∧
      ∀ ρ : Matrix (Bits m) (Bits m) ℂ,
        ((Fintype.card (PauliIdx m) : ℂ)⁻¹ • ∑ P : PauliIdx m,
            (pauliOp P)ᴴ * E.apply (pauliOp P * ρ * (pauliOp P)ᴴ) * pauliOp P) =
          ∑ Q ∈ Finset.univ.filter (fun Q : PauliIdx m => pauliWeight Q.2.1 Q.2.2 ≤ t),
            ((p Q : ℂ) • (pauliOp Q * ρ * (pauliOp Q)ᴴ)) := by sorry

end QuantumPRC
