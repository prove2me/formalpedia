-- Prove2me | Theorems.Thm_SquashedKey_eq_6_twisted_form
-- name    : SquashedKey.eq_6_twisted_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:33:29.870717+00:00
-- url     : https://prove2.me/theorems/23caaae3-4e59-47fe-87f0-e1ca1c05a9cd
-- title:
--   Eqs. (6)–(8) — every private state is $U(\Phi_{AB}\otimes\sigma_{A'B'})U^\dagger$ for a twisting unitary $U$
-- statement:
--   Let $\gamma_{ABA'B'}$ be a private state of $\log_2K$ private bits in the sense of (5), with shields $A'$, $B'$ of arbitrary dimension. Then there are a state $\sigma_{A'B'}$ and unitaries $U^{ij}_{A'B'}$ ($0\le i,j<K$) such that
--   $$
--   \gamma_{ABA'B'}=U_{ABA'B'}\,(\Phi_{AB}\otimes\sigma_{A'B'})\,U^\dagger_{ABA'B'},
--   $$
--   where $\Phi_{AB}=\frac1K\sum_{i,j}|i\rangle\langle j|_A\otimes|i\rangle\langle j|_B$ is the maximally entangled state of Schmidt rank $K$ and $U_{ABA'B'}=\sum_{i,j}|i\rangle\langle i|_A\otimes|j\rangle\langle j|_B\otimes U^{ij}_{A'B'}$ is the twisting unitary.
--
--   This structure is what makes the entropies in the proof of Lemma 1 computable.
--
--   **Formalization Note** Private states are defined by (5) (`IsPrivateState`); `twistedState σ U` is the coefficient array of $U(\Phi\otimes\sigma)U^\dagger$.
--
--   Differences from the source:
--
--   - reading: γ 'is called a private state' if (5) holds for any purification; the twisted form (6) is 'a non-trivial consequence' → IsPrivateState γ: (5) holds for every unit vector φ on every purifying system E : Type with Tr_E |φ⟩⟨φ| = γ; reason: (5) is the definition printed on p.4; (6) is stated as a theorem of the mission (eq_6_twisted_form)
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: registers ordered ABA′B′ → registers ordered (AA′)(BB′), basis index ((a,s),(b,t)); reason: a relabelling of tensor factors; the same operator
--   - encoding: U_{ABA′B′} = Σ_{i,j} |i⟩⟨i|_A ⊗ |j⟩⟨j|_B ⊗ U^{ij}_{A′B′} → a family U : Fin K → Fin K → unitary operators on ℓ²(A′ × B′); γ's coefficient array equals twistedState σ U; reason: twistedState is the coefficient formula of U(Φ⊗σ)U†, block (a,b),(a′,b′) equal to δ_{ab}δ_{a′b′}(1/K)U^{aa}σ(U^{a′a′})† as in (35)
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eqs. (6)–(8), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_SquashedKey_PrivateState
import Definitions.Def_SquashedKey_Twisting

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

namespace SquashedKey

/-- **Twisted form of a private state, (6)–(8)**, Wilde, *Squashed entanglement and approximate
private states*, arXiv:1606.08028v3, §2.3, (6)–(8), p.4 (PDF p.4): "It is a non-trivial consequence
of the above definition that a private state of `log₂ K` private bits can be written in the
following form: `γ_{ABA′B′} = U_{ABA′B′} (Φ_{AB} ⊗ σ_{A′B′}) U†_{ABA′B′}`, (6) where `Φ_{AB}` is a
maximally entangled state of Schmidt rank `K`, `Φ_{AB} ≡ (1/K) Σ_{i,j} |i⟩⟨j|_A ⊗ |i⟩⟨j|_B`, (7) and
`U_{ABA′B′} = Σ_{i,j} |i⟩⟨i|_A ⊗ |j⟩⟨j|_B ⊗ U^{ij}_{A′B′}` (8) is a controlled unitary known as a
'twisting unitary,' with each `U^{ij}_{A′B′}` a unitary operator."

For every `K`, all shield types `A′`, `B′` and every private state `γ` (definition (5)), there are
a state `σ` on `A′B′` and unitaries `U^{ij}` on `ℓ²(A′ × B′)` with `γ = U (Φ ⊗ σ) U†`.

**Formalization Note** The shields are arbitrary types (any dimension, infinite included). A private
state is defined by (5) (`IsPrivateState`), and `twistedState σ U` is the coefficient array of
`U (Φ ⊗ σ) U†`. -/
theorem eq_6_twisted_form {K : ℕ} {A' B' : Type} (γ : State ((Fin K × A') × (Fin K × B')))
    (hγ : IsPrivateState γ) :
    ∃ (σ : State (A' × B')) (U : TwistingUnitary K A' B'),
      γ.coefficients = twistedState σ.coefficients U := by sorry

end SquashedKey
