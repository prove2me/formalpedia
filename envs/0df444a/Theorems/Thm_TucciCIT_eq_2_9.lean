-- Prove2me | Theorems.Thm_TucciCIT_eq_2_9
-- name    : TucciCIT.eq_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:54.37853+00:00
-- url     : https://prove2.me/theorems/c4a0e908-1820-4e98-9d7f-ec532d740883
-- title:
--   Eq. (2.9) and (4.11) — $E_F$ is local-unitary invariant and equals $-\sum_x p_x\log_2 p_x$
-- statement:
--   Two statements.
--
--   1. For every amplitude matrix $\psi$ and all unitaries $U$ on $\mathcal H_x$ and $V$ on $\mathcal H_y$,
--   $$
--   E_F(U\psi V^\dagger) = E_F(\psi).
--   $$
--   2. For an injection $e : S_x \hookrightarrow S_y$ and numbers $p_x \ge 0$, the "diagonal" matrix $\tilde\psi$ with $\tilde\psi_{xy} = \sqrt{p_x}$ if $y = e(x)$ and $0$ otherwise satisfies
--   $$
--   E_F(\tilde\psi) = -\sum_x p_x \log_2 p_x
--   $$
--   (with $0\log 0 = 0$).
--
--   Together with the singular value decomposition this gives $E_F(\psi) = E_F(\tilde\psi) = -\sum_x p_x\log_2 p_x$ (2.9), and part 1 is the last equality $E_F(\psi^0) = E_F(\psi)$ of (4.11) for $\psi = U\psi^0V^\dagger$.
--
--   Differences from the source:
--   - generalization: EF(ψ) = EF(ψ̃) for the U, V of the SVD (2.5), and EF(ψ⁰) = EF(Uψ⁰V†) in (4.11) → EF(UψV†) = EF(ψ) for all unitaries U, V and every ψ; reason: (4.11) already uses arbitrary U, V; normalization is not needed
--   - generalization: p_x the (normalized) singular values squared from (2.6) → any p_x ≥ 0; reason: the value of EF on the diagonal form holds for every nonnegative p; it specializes to the SVD's p
--   - encoding: ψ̃ diagonal with rows and columns numbered alike → ψ̃ supported on the graph of an injection e : X ↪ Y; reason: X and Y are unordered finite types
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (2.9), p.4, and the last equality of eq. (4.11), p.9

import Mathlib
import Definitions.Def_TucciCIT_entanglementOfFormation

open scoped Matrix

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (2.9), p.4 (PDF p.4): "By Eq.(2.4) and (2.6),
EF(ψxy) = EF(ψ̃x,y) = −Σx px log2 px", and the last equality of eq. (4.11), p.9:
"EF(ψ⁰xy) = EF(ψxy)" for `ψ = Uψ⁰V†`.

Two parts:
1. local-unitary invariance: for every amplitude `ψ` and all unitaries `U` on `H_x` and `V` on
   `H_y`, `EF(UψV†) = EF(ψ)`;
2. the value on the diagonal form: for an injection `e : S_x ↪ S_y` and numbers `p_x ≥ 0`, the
   matrix `ψ̃` with `ψ̃_{xy} = √p_x` if `y = e(x)` and `0` otherwise has
   `EF(ψ̃) = −Σ_x p_x log₂ p_x` (with `0 log 0 = 0`).

**Formalization Note.** `ψ̃` is the diagonal form produced by the SVD milestone (eqs. (2.5)–(2.6)).
Part 2 does not assume `Σ p_x = 1`. -/
theorem eq_2_9 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    (∀ (ψ : Matrix X Y ℂ) (U : Matrix.unitaryGroup X ℂ) (V : Matrix.unitaryGroup Y ℂ),
      entanglementOfFormation ((U : Matrix X X ℂ) * ψ * (V : Matrix Y Y ℂ)ᴴ) =
        entanglementOfFormation ψ) ∧
    ∀ (e : X ↪ Y) (p : X → ℝ), (∀ x, 0 ≤ p x) →
      entanglementOfFormation
          (Matrix.of fun x y => if y = e x then ((Real.sqrt (p x) : ℝ) : ℂ) else 0) =
        -∑ x, p x * Real.logb 2 (p x) := by sorry

end TucciCIT
