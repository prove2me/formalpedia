-- Prove2me | Theorems.Thm_TucciCIT_eq_4_15
-- name    : TucciCIT.eq_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:16.618579+00:00
-- url     : https://prove2.me/theorems/c4a4db92-8d10-4890-83c0-bec006012cb3
-- title:
--   Eq. (4.15) — $S_\mu(x:y|e) \le E_F(\psi)$
-- statement:
--   Let $\psi$ be a unit amplitude on finite sets $S_x$, $S_y$ of any sizes, $\sum_{x,y}|\psi(x,y)|^2 = 1$, and $\mu$ its meta density matrix. Then
--
--   $$
--   S_\mu(x : y|e) \le E_F(\psi).
--   $$
--
--   This is the upper-bound half of the main theorem: for every pair of a priori local unitaries the S-tanglement does not exceed the entanglement of formation.
--
--   **Formalization Note** The paper derives (4.15) from its eqs. (4.13) and (4.14). Eq. (4.13), $E_F(|\psi|) \le E_F(\psi)$, is false for $N_x = N_y = 3$: for $\psi = \tfrac{1}{\sqrt6}\begin{pmatrix}0&1&1\\-1&0&1\\-1&-1&0\end{pmatrix}$ one has $E_F(\psi) = 1$ but $E_F(|\psi|) = \log_2 3 - \tfrac13$. Inequality (4.15) itself is true: it follows from strong subadditivity applied to the reduction of $\mu$ to the registers $(e_2, x, e_1)$, whose four entropies are $H(x,y)$, $E_F(\psi)$, $H(x)$ and $H(y)$.
--
--   Differences from the source:
--   - generalization: Nx ≤ Ny (assumed without loss of generality, p.8) → no size relation between X and Y; reason: the case Ny < Nx follows by exchanging the listeners; the statement specializes to Nx ≤ Ny
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.15), p.10

import Mathlib
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement
import Definitions.Def_TucciCIT_entanglementOfFormation

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.15), p.10 (PDF p.10): "Combining these inequalities and
Eq.(4.8) yields Sµ(x : y|e) ≤ EF(ψxy)."

For every unit amplitude `ψ` (`Σ_{x,y} |ψ(x,y)|² = 1`) on finite `S_x`, `S_y` of any sizes, the
S-tanglement of its meta density matrix is at most its entanglement of formation:
`S_μ(x : y|e) ≤ EF(ψ)`.

**Formalization Note.** The paper derives this from its eqs. (4.13) and (4.14). Eq. (4.13),
`EF(|ψ|) ≤ EF(ψ)`, is false for `N_x = N_y = 3` (e.g. `ψ = (1/√6)[[0,1,1],[−1,0,1],[−1,−1,0]]`:
`EF(ψ) = 1`, `EF(|ψ|) = log₂ 3 − 1/3`), and is not used here; (4.15) itself is true (it follows
from strong subadditivity applied to the reduction of `μ` to `(e₂, x, e₁)`). No `N_x ≤ N_y` is
assumed. -/
theorem eq_4_15 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) (hψ : ∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1) :
    sTanglement (metaDensity ψ) ≤ entanglementOfFormation ψ := by sorry

end TucciCIT
