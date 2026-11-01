-- Prove2me | Theorems.Thm_SquashedKey_eq_9_extension_form
-- name    : SquashedKey.eq_9_extension_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:32:28.300761+00:00
-- url     : https://prove2.me/theorems/6c17e90a-adf8-44dd-903e-33cb3b3eb7d7
-- title:
--   Eq. (9) — every extension of a private state is $U(\Phi_{AB}\otimes\sigma_{A'B'E})U^\dagger$ with $\sigma_{A'B'E}$ extending $\sigma_{A'B'}$
-- statement:
--   Let $\gamma_{AA'BB'}=U(\Phi_{AB}\otimes\sigma_{A'B'})U^\dagger$ be a state in the twisted form (6), for a state $\sigma_{A'B'}$ and a twisting unitary $U$. Let $E$ be any system and $\gamma_{AA'BB'E}$ any extension of $\gamma_{AA'BB'}$. Then there is an extension $\sigma_{A'B'E}$ of $\sigma_{A'B'}$ such that
--   $$
--   \gamma_{AA'BB'E}=U_{AA'BB'}\,(\Phi_{AB}\otimes\sigma_{A'B'E})\,U^\dagger_{AA'BB'},
--   $$
--   with the same twisting unitary $U$ (acting as the identity on $E$).
--
--   Formula (35), on which the proof of (33) rests, is this identity written out.
--
--   **Formalization Note** The hypothesis is the representation (6) itself, for whichever $\sigma$ and $U$ realize it; $E$, $A'$, $B'$ are arbitrary types and `twistedExtension` is the coefficient array of the right-hand side.
--
--   Differences from the source:
--
--   - generalization: γ a private state, with σ and U those of its form (6) → γ = U(Φ⊗σ)U† for any state σ and any twisting unitary U; the conclusion uses that same U; reason: by (6) every private state has such a representation, so the paper's claim is the instance with the representation of (6); conversely every twisted state is private (the easy direction (6) ⇒ (5))
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: registers ordered ABA′B′ → registers ordered (AA′)(BB′), basis index ((a,s),(b,t)); reason: a relabelling of tensor factors; the same operator
--   - encoding: U_{AA′BB′} (Φ_{AB} ⊗ σ_{A′B′E}) U†_{AA′BB′} → twistedExtension σE U, computed block by block in E: block (e,e′) is (U^{aa}) σ_{ee′} (U^{a′a′})†; reason: (U ⊗ 1_E) X (V ⊗ 1_E)† has (e,e′) block U X_{ee′} V†; the same operator
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eq. (9), pp.4–5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_SquashedKey_Twisting

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceSecond)

namespace SquashedKey

/-- **Form of every extension of a private state, (9)**, Wilde, *Squashed entanglement and
approximate private states*, arXiv:1606.08028v3, §2.3, (9), pp.4–5 (PDF pp.4–5): "Any extension
`γ_{AA′BB′E} ∈ D(H_{AA′BB′E})` of a private state `γ_{AA′BB′}` necessarily has the following form:
`γ_{AA′BB′E} = U_{AA′BB′} (Φ_{AB} ⊗ σ_{A′B′E}) U†_{AA′BB′}`, (9) where `σ_{A′B′E}` is an extension
of `σ_{A′B′}`."

Let `γ = U (Φ ⊗ σ) U†` be a state in the twisted form (6) (state `σ` on `A′B′`, twisting unitary
`U`). Then for every system `E` and every state `γ_E` on `AA′BB′E` with `Tr_E γ_E = γ`, there is a
state `σ_E` on `A′B′E` with `Tr_E σ_E = σ` and `γ_E = (U ⊗ 1_E)(Φ ⊗ σ_E)(U ⊗ 1_E)†`, with the
same `U`.

**Formalization Note** The hypothesis is the representation (6) itself, for any `σ` and `U`
realizing it, rather than "γ is private" with `σ`, `U` from (6): every state of the form (6) is a
private state, so this covers the paper's claim. `E`, `A′`, `B′` are arbitrary types. -/
theorem eq_9_extension_form {K : ℕ} {A' B' : Type} (γ : State ((Fin K × A') × (Fin K × B')))
    (σ : State (A' × B')) (U : TwistingUnitary K A' B')
    (hγ : γ.coefficients = twistedState σ.coefficients U)
    (E : Type) (γE : State (FiveParty K A' B' E))
    (hE : partialTraceSecond γE.coefficients = γ.coefficients) :
    ∃ σE : State ((A' × B') × E), partialTraceSecond σE.coefficients = σ.coefficients ∧
      γE.coefficients = twistedExtension σE.coefficients U := by sorry

end SquashedKey
