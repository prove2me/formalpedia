-- Prove2me | Theorems.Thm_TucciCIT_eq_4_3
-- name    : TucciCIT.eq_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:20.213194+00:00
-- url     : https://prove2.me/theorems/37b37d4f-5bc0-45d0-ba40-83e3292d6b10
-- title:
--   Eq. (4.3) — $\operatorname{tr}_e\mu$ is diagonal with entries $|\psi(x,y)|^2$
-- statement:
--   Let $\psi$ be an amplitude on $S_x \times S_y$ and $\mu$ its meta density matrix (4.1). Then the reduced density matrix on $(x, y)$ is
--
--   $$
--   \rho = \operatorname{tr}_e(\mu) = \sum_{x,y} \psi(x,y)\psi^*(x,y)\,|x, y\rangle\langle x, y| ,
--   $$
--
--   diagonal in the $|x,y\rangle$ basis.
--
--   Because $\rho$ is diagonal, its entropies are classical entropies of $P(x,y) = |\psi(x,y)|^2$, which is what reduces (4.6) to (4.8).
--
--   **Formalization Note** $\operatorname{tr}_e$ is the platform partial trace keeping the coordinates $(x,y)$ and tracing out $e$.
--
--   Differences from the source:
--   - generalization: μ built from a unit amplitude → μ built from any amplitude ψ; reason: the computation of tr_e μ does not use normalization; it specializes to the paper's μ
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.3), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_TucciCIT_metaDensity

open QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.3), p.8 (PDF p.8): "Define ρ by
ρ = tr_e(µ) = Σ_ri ψ(x, y)ψ∗(x, y)|x, y⟩⟨x, y|."

For every amplitude `ψ`, the partial trace over `e` of the meta density matrix `μ` (4.1) is the
diagonal matrix on `S_x × S_y` with entries `ψ(x,y) ψ*(x,y) = |ψ(x,y)|²`.

**Formalization Note.** `tr_e` is `redistributionMarginal μ keep forget` with `keep p = (x, y)`
and `forget p = e`. The sum over repeated indices `Σ_ri` is the diagonal. -/
theorem eq_4_3 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) :
    redistributionMarginal (metaDensity ψ) (fun p => p.2) (fun p => p.1) =
      Matrix.diagonal (fun q : X × Y => ψ q.1 q.2 * star (ψ q.1 q.2)) := by sorry

end TucciCIT
