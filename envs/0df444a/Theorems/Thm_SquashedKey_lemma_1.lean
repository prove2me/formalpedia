-- Prove2me | Theorems.Thm_SquashedKey_lemma_1
-- name    : SquashedKey.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:33:01.156313+00:00
-- url     : https://prove2.me/theorems/36f435ff-fa66-4b46-afc7-ab71c81e1ed0
-- title:
--   Lemma 1 — for any extension of a private state, $2\log_2K=I(A;BB'|E)_\gamma+I(A';B|AB'E)_\gamma$
-- statement:
--   Let $\gamma_{AA'BB'}$ be a bipartite private state of $\log_2K$ private bits (definition (5)), with shields of arbitrary dimension, and let $\gamma_{AA'BB'E}$ be any extension of it on any system $E$. Then
--   $$
--   2\log_2K=I(A;BB'|E)_\gamma+I(A';B|AB'E)_\gamma .
--   $$
--
--   This exact identity is the first step (48) of the proof of Theorem 2: it splits the key $2\log_2K$ into two conditional mutual informations, in each of which one of the correlated systems is a $K$-dimensional key system.
--
--   **Formalization Note** Information quantities are the extended conditional mutual information in bits, in $[0,+\infty]$; $2\log_2K$ enters as `ENNReal.ofReal (2 * Real.logb 2 K)`.
--
--   Differences from the source:
--
--   - reading: I(A;B|E) = H(AE)+H(BE)−H(E)−H(ABE) (15), which is ∞ − ∞ when the entropies are infinite → Shirokov's extended conditional mutual information (published qcmi: supremum over finite-rank projectors P on A of I(PA;BE) − I(PA;E)) divided by ln 2, valued in ℝ≥0∞; reason: the paper allows infinite-dimensional shields and extensions and takes (21) from [Shi17], which is proved for this quantity; it equals (15) whenever the entropies in (15) are finite, so it changes no instance on which (15) is defined
--   - reading: γ 'is called a private state' if (5) holds for any purification; the twisted form (6) is 'a non-trivial consequence' → IsPrivateState γ: (5) holds for every unit vector φ on every purifying system E : Type with Tr_E |φ⟩⟨φ| = γ; reason: (5) is the definition printed on p.4; (6) is stated as a theorem of the mission (eq_6_twisted_form)
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: real-valued log₂ K and information quantities → information quantities in ℝ≥0∞, real terms entered through ENNReal.ofReal; reason: the quantities are nonnegative and may be +∞ in infinite dimension; ENNReal.ofReal of a nonnegative real is that real (log₂ K ≥ 0 for K ≥ 1, and for K = 0 there is no state)
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, Lemma 1, eq. (31), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_SquashedKey_PrivateState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceSecond)

namespace SquashedKey

/-- **Lemma 1**, Wilde, *Squashed entanglement and approximate private states*,
arXiv:1606.08028v3, Lemma 1, (31), p.7 (PDF p.7): "Let `γ_{AA′BB′}` be a bipartite private state and
let `γ_{AA′BB′E}` be an extension of it, as defined in Section 2.3. Then the following identity holds
for any such extension: `2 log₂ K = I(A; BB′|E)_γ + I(A′; B|AB′E)_γ`."

For every `K`, all shield types `A′`, `B′`, every private state `γ` (definition (5)), every system
`E` and every state `γ_E` on `AA′BB′E` with `Tr_E γ_E = γ`:
`2 log₂ K = I(A; BB′|E)_{γ_E} + I(A′; B|AB′E)_{γ_E}`.

**Formalization Note** Information quantities are the extended conditional mutual information in
bits, in `ℝ≥0∞`; `2 log₂ K` enters as `ENNReal.ofReal (2 * Real.logb 2 K)`. `E`, `A′`, `B′` are
arbitrary types. -/
theorem lemma_1 {K : ℕ} {A' B' : Type} (γ : State ((Fin K × A') × (Fin K × B')))
    (hγ : IsPrivateState γ) (E : Type) (γE : State (FiveParty K A' B' E))
    (hE : partialTraceSecond γE.coefficients = γ.coefficients) :
    ENNReal.ofReal (2 * Real.logb 2 (K : ℝ)) =
      infoA_BBp_E γE.coefficients + infoAp_B_ABpE γE.coefficients := by sorry

end SquashedKey
