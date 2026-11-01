-- Prove2me | Theorems.Thm_TucciCIT_max_sTanglement_eq_entanglementOfFormation
-- name    : TucciCIT.max_sTanglement_eq_entanglementOfFormation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:13.331703+00:00
-- url     : https://prove2.me/theorems/4d0b3874-342a-45af-9e2e-ceb90cdc7648
-- title:
--   §4 closing statement — S-tanglement maximized over a priori local unitaries equals $E_F$
-- statement:
--   Let $S_x$ and $S_y$ be finite sets and $\psi^0$ a unit amplitude, $\sum_{x,y}|\psi^0(x,y)|^2 = 1$. For unitaries $U$ on $\mathcal H_x$ and $V$ on $\mathcal H_y$ let $\mu_{U,V}$ be the meta density matrix of the net of Fig. 3 whose speaker $e$ carries the rotated amplitude
--
--   $$
--   \psi = U\psi^0V^\dagger
--   $$
--
--   (a priori local unitary transformations on the listeners, first table on p. 8). Then $E_F(\psi^0)$ is the greatest element of the set
--
--   $$
--   \{\, S_{\mu_{U,V}}(x : y\,|\,e) \;:\; U, V \text{ unitary} \,\}:
--   $$
--
--   some pair $(U, V)$ attains $S_{\mu_{U,V}}(x:y|e) = E_F(\psi^0)$, and every pair satisfies $S_{\mu_{U,V}}(x:y|e) \le E_F(\psi^0)$. In words: maximized over all a priori local unitary transformations on its two listeners, the S-tanglement equals the entanglement of formation.
--
--   This is the paper's main identification of its new entanglement measure with the standard one for pure states.
--
--   **Formalization Note** "Maximized … equals EF" is stated with `IsGreatest`, which carries both the bound and its attainment and avoids a real supremum. Entropies are in bits, $S(A|E) = S(A,E) - S(E)$, and $E_F$ is the pure-state quantity (2.1).
--
--   Differences from the source:
--   - reading: if ST is maximized over all a priori local unitaries U and V, then it equals EF → IsGreatest of the set of S-tanglements over all (U, V), with value EF(ψ⁰); reason: the paragraph asserts both attainment (4.12) and the bound (4.15); IsGreatest states both
--   - reading: the corresponding EF, i.e. EF(ψ) for ψ = Uψ⁰V† → EF(ψ⁰); reason: EF(ψ⁰) = EF(ψ) by the last equality of (4.11); the paper treats it as one number
--   - generalization: Nx ≤ Ny (assumed without loss of generality, pp.3, 8) → no size relation between X and Y; reason: the case Ny < Nx follows by exchanging listeners; the statement specializes to Nx ≤ Ny
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, §4, closing paragraph (Eqs. 4.12, 4.15), p.10

import Mathlib
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement
import Definitions.Def_TucciCIT_entanglementOfFormation

open scoped Matrix

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, §4, closing paragraph (eqs. (4.12), (4.15)), p.10 (PDF p.10):
"there exists a pair of unitary matrices U and V so that the S-tanglement ST equals the
corresponding entanglement of formation EF. … for any U and V, ST is less than or equal to the
corresponding EF. Therefore, if ST is maximized over all a priori local unitary transformations
U and V on its two listeners, then it equals EF."

Let `S_x`, `S_y` be finite sets and `ψ⁰` a unit amplitude, `Σ_{x,y} |ψ⁰(x,y)|² = 1`. For unitaries
`U` on `H_x` and `V` on `H_y`, let `μ_{U,V}` be the meta density matrix (4.1) of the a priori net
of the first table on p.8, whose speaker `e` carries the rotated amplitude `ψ = Uψ⁰V†` (eq. (4.9)).
Then `EF(ψ⁰)` is the greatest value of `S_{μ_{U,V}}(x : y|e)` over all pairs `(U, V)`: it is
attained by some pair, and no pair exceeds it.

**Formalization Note.** "Maximized … equals EF" is `IsGreatest` of the set of values, which
contains both the bound and attainment. "The corresponding EF" is `EF(Uψ⁰V†)`, which equals
`EF(ψ⁰)` (last equality of (4.11)); the statement uses `EF(ψ⁰)`. `S(A|E) = S(A,E) − S(E)`;
entropies in bits; EF is the pure-state EF of eq. (2.1). The paper's "without loss of generality
`N_x ≤ N_y`" is not assumed: the statement covers all sizes. -/
theorem max_sTanglement_eq_entanglementOfFormation {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (ψ₀ : Matrix X Y ℂ) (hψ₀ : ∑ x, ∑ y, ‖ψ₀ x y‖ ^ 2 = 1) :
    IsGreatest
      (Set.range fun UV : Matrix.unitaryGroup X ℂ × Matrix.unitaryGroup Y ℂ =>
        sTanglement (metaDensity ((UV.1 : Matrix X X ℂ) * ψ₀ * (UV.2 : Matrix Y Y ℂ)ᴴ)))
      (entanglementOfFormation ψ₀) := by sorry

end TucciCIT
