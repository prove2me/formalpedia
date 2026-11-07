-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_11
-- name    : QMAPlusGap.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:26.871134+00:00
-- url     : https://prove2.me/theorems/41405eb0-a066-420b-8eb9-836ed84f0cdc
-- title:
--   Lemma 11 — $\operatorname{Tr}[P^{(2N)}_{\mathrm{sym}}(X\otimes Y)]$ in terms of reductions
-- statement:
--   Let $X,Y$ be subnormalized positive semidefinite operators on $\mathcal H^{\otimes N}$ supported on $\mathrm{Sym}^N(\mathcal H)$, and let $X_j,Y_j$ be their reductions to $j$ registers ($X_0=\operatorname{Tr}X$, $Y_0=\operatorname{Tr}Y$). Then
--   $$
--   \operatorname{Tr}\big[P^{(2N)}_{\mathrm{sym}}(X\otimes Y)\big]=\frac{1}{\binom{2N}{N}}\sum_{j=0}^{N}\binom Nj^{2}\operatorname{Tr}(X_jY_j).\tag{9}
--   $$
--
--   The identity decomposes the joint symmetric test of the protocol into overlaps of reductions with a hypergeometric weight, which Proposition 9 then bounds sector by sector.
--
--   Differences from the source:
--   - encoding: X ⊗ Y on 2N registers; reductions to j registers; subnormalized → tensorJoin X Y on N + N registers with X on the first N; reduce j keeps the first j registers; Tr X ≤ 1; reason: for operators supported on Sym^N every choice of j registers gives the same reduction
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 11, p.20 (convention X₀ = Tr X, p.22)

import Mathlib
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_QMAPlusGap_tensorJoin

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma 11**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.20: "Let X, Y be subnormalized positive semidefinite operators supported on Sym^N(H), and
let X_j, Y_j be their reductions to j registers. Then
Tr[P_sym^{(2N)}(X ⊗ Y)] = (1/C(2N, N)) Σ_{j=0}^{N} C(N, j)² Tr(X_j Y_j). (9)"

**Formalization Note** `H = ℂ^ι`; `X ⊗ Y` acts on `N + N` registers with `X` on the first `N`
(`tensorJoin`); `X_j = reduce j X` keeps the first `j` registers, and `X_0 = reduce 0 X` is `Tr X` (p.22).
"Subnormalized" is `Tr X ≤ 1`. -/
theorem lemma_11 {ι : Type} [Fintype ι] [DecidableEq ι] (N : ℕ) (X Y : Matrix (Fin N → ι) (Fin N → ι) ℂ)
    (hX : X.PosSemidef) (hXt : (Matrix.trace X).re ≤ 1) (hY : Y.PosSemidef) (hYt : (Matrix.trace Y).re ≤ 1)
    (hXs : IsSymSupported X) (hYs : IsSymSupported Y) :
    Matrix.trace (symProj (N + N) * tensorJoin X Y) =
      (((2 * N).choose N : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (N + 1), ((N.choose j : ℂ)) ^ 2 * Matrix.trace (reduce j X * reduce j Y) := by sorry

end QMAPlusGap
