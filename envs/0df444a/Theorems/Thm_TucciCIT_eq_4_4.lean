-- Prove2me | Theorems.Thm_TucciCIT_eq_4_4
-- name    : TucciCIT.eq_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:21.978642+00:00
-- url     : https://prove2.me/theorems/2bb664dc-dd63-498b-a06e-13980c6cdb84
-- title:
--   Eq. (4.4) — $S_\mu(x:y|e)$ as four entropies
-- statement:
--   Let $\psi$ be an amplitude on $S_x \times S_y$ and $\mu$ the meta density matrix (4.1). Then the S-tanglement satisfies
--
--   $$
--   S_\mu(x : y|e) = S_\mu(x, e) + S_\mu(y, e) - S_\mu(x, y, e) - S_\mu(e).
--   $$
--
--   This rewrites the conditional form (3.2) as a signed sum of four marginal entropies of $\mu$, the starting point of §4.
--
--   Differences from the source:
--   - generalization: μ built from a unit amplitude ψ = Uψ⁰V† → μ built from any amplitude ψ; reason: the identity is algebraic in the four entropies and holds for every ψ; it specializes to the paper's μ
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
--   - encoding: S_μ of a set of nodes → subsystemEntropy μ keep forget, with keep the kept coordinates of (e, x, y) in a fixed order; reason: entropy is invariant under reordering the kept registers; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.4), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.4), p.8 (PDF p.8): "One has that
Sµ(x : y|e) = Sµ(x, e) + Sµ(y, e) − Sµ(x, y, e) − Sµ(e)."

For the meta density matrix `μ` of eq. (4.1), built from any amplitude `ψ`, the S-tanglement
`S_μ(x : y|e)` of eq. (3.2) equals `S_μ(x, e) + S_μ(y, e) − S_μ(x, y, e) − S_μ(e)`.

**Formalization Note.** `S_μ(x, e)` keeps the coordinates `(e, x)` and traces out `y`;
`S_μ(y, e)` keeps `(e, y)`; `S_μ(e)` keeps `e`; `S_μ(x, y, e) = vnEntropy μ`. -/
theorem eq_4_4 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) :
    sTanglement (metaDensity ψ) =
      subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.1)) (fun p => p.2.2) +
        subsystemEntropy (metaDensity ψ) (fun p => (p.1, p.2.2)) (fun p => p.2.1) -
        vnEntropy (metaDensity ψ) -
        subsystemEntropy (metaDensity ψ) (fun p => p.1) (fun p => p.2) := by sorry

end TucciCIT
