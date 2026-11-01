-- Prove2me | Theorems.Thm_TucciCIT_eq_4_12
-- name    : TucciCIT.eq_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:47.280187+00:00
-- url     : https://prove2.me/theorems/8296d112-52e1-402f-89a5-d732accb7385
-- title:
--   Eq. (4.12) — $S_\mu(x:y|e) = E_F(\psi)$ when $U, V$ make $\psi$ diagonal
-- statement:
--   Let $e : S_x \hookrightarrow S_y$ be an injection (so $N_x \le N_y$) and let $\psi$ be a unit amplitude that is diagonal along $e$: $\psi(x,y) = 0$ whenever $y \ne e(x)$. Then
--
--   $$
--   S_\mu(x : y|e) = E_F(\psi),
--   $$
--
--   where $\mu$ is the meta density matrix of $\psi$.
--
--   This is the attainment half of the main theorem: by the singular value decomposition some pair $U, V$ makes $\psi = U\psi^0V^\dagger$ diagonal, and there the S-tanglement equals the entanglement of formation.
--
--   **Formalization Note** $\psi$ is the rotated amplitude; the hypothesis "U and V make ψ diagonal" is the support condition along $e$. The diagonal entries may be arbitrary complex numbers.
--
--   Differences from the source:
--   - encoding: ψ diagonal (ψxy = 0 if x ≠ y), Nx ≤ Ny → ψ x y = 0 whenever y ≠ e x, for an injection e : X ↪ Y; reason: X and Y are unordered finite types; the injection identifies rows with the first Nx columns
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.12), p.9

import Mathlib
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement
import Definitions.Def_TucciCIT_entanglementOfFormation

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.12), p.9 (PDF p.9): "Combining the last equation and
Eq.(4.8) yields Sµ(x : y|e) = EF(ψxy) for the special case that U and V make ψ diagonal."

Let `e : S_x ↪ S_y` (so `N_x ≤ N_y`) and let `ψ` be a unit amplitude that is diagonal along `e`:
`ψ(x, y) = 0` whenever `y ≠ e(x)`. Then the S-tanglement of its meta density matrix equals its
entanglement of formation: `S_μ(x : y|e) = EF(ψ)`.

**Formalization Note.** `ψ` is the already rotated amplitude `Uψ⁰V†` (eq. (4.9)); the hypothesis
`hdiag` is "U and V make ψ diagonal", with the paper's `x = y` read through `e`. The diagonal
entries may be any complex numbers. -/
theorem eq_4_12 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) (ψ : Matrix X Y ℂ) (hψ : ∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1)
    (hdiag : ∀ x y, y ≠ e x → ψ x y = 0) :
    sTanglement (metaDensity ψ) = entanglementOfFormation ψ := by sorry

end TucciCIT
