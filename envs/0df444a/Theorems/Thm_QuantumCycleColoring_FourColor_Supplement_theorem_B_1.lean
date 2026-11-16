-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_Supplement_theorem_B_1
-- name    : QuantumCycleColoring.FourColor.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:33:16.232744+00:00
-- url     : https://prove2.me/theorems/4b912d45-1218-4189-bce9-a0bb1b5cb500
-- title:
--   Theorem B.1: total $\Lambda$-energy of $2$- and $3$-outcome POVMs is at least $1/8$ and $1/2916$
-- statement:
--   Let $\Lambda\in\mathbb C^{N\times N}$ be PSD with $\|\Lambda\|_F=1$, and write $\mathcal E_\Lambda(P)=\mathrm{Tr}(\Lambda A\Lambda B)$ for the **$\Lambda$-energy** of a PSD operator $P$ on $\mathbb C^N\otimes\mathbb C^N$, with $A=\mathrm{Tr}_{\mathcal A}((\Lambda^2\otimes I)P)^\top$, $B=\mathrm{Tr}_{\mathcal B}((I\otimes\bar\Lambda^2)P)$. Fix $q\in\{2,3\}$. For every POVM $\{P_i\}_{i\in[q]}$ on $\mathbb C^N\otimes\mathbb C^N$,
--   $$\sum_{i=1}^{q}\mathcal E_\Lambda(P_i)\ \ge\ C_q,\qquad C_q=\begin{cases}1/8,& q=2,\\ 1/2916,& q=3.\end{cases}$$
--
--   This is statement (Q1) of Theorem 6.1 for two and three colours with explicit constants, so one-way one-round quantum algorithms cannot colour directed cycles with at most three colours with high probability. The proof is operator-theoretic and independent of the bounded-dependence argument of §6.2.
--
--   Differences from the source:
--   - encoding: Λ-energy E_Λ(P) = Tr(ΛAΛB), a complex trace that is real for PSD P, Λ → energy Λ P is the real part of this trace; reason: the trace is real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: fix q ∈ {2, 3}, outcomes i = 1, …, q, constant C_q by cases → a conjunction of the q = 2 statement with constant 1/8 and the q = 3 statement with constant 1/2916, outcomes Fin q; reason: the two cases of the source, stated separately; the same instances
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem B.1, p.53 (proof pp.53–54)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor.Supplement

open QuantumCycleColoring.FourColor Matrix

/-- Theorem B.1, p.53 (Gur–Li, STOC 2027 #515). Fix `q ∈ {2, 3}`. For every POVM `{P_i}_{i∈[q]}`
on `ℂ^N ⊗ ℂ^N` and every PSD `Λ` with `‖Λ‖_F = 1`, `∑_{i=1}^q E_Λ(P_i) ≥ C_q`, where
`C_2 = 1/8` and `C_3 = 1/2916`. -/
theorem theorem_B_1 {d : Type} [Fintype d] [DecidableEq d]
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛF : frobNorm Λ = 1) :
    (∀ P : Fin 2 → Matrix (d × d) (d × d) ℂ, FuchsVdGraaf.IsPOVM P →
      (1 / 8 : ℝ) ≤ ∑ i, energy Λ (P i)) ∧
    (∀ P : Fin 3 → Matrix (d × d) (d × d) ℂ, FuchsVdGraaf.IsPOVM P →
      (1 / 2916 : ℝ) ≤ ∑ i, energy Λ (P i)) := by sorry

end QuantumCycleColoring.FourColor.Supplement
