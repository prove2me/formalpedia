-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_proposition_4_12
-- name    : QuantumSymmetryBreaking.CycleColoring.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:12.98186+00:00
-- url     : https://prove2.me/theorems/699eed33-90fd-406a-8dec-10a54ddebc24
-- title:
--   Proposition 4.12 — the binomial square-root series converges in $\|\cdot\|_w$
-- statement:
--   Let $Y\in\mathbb C[G\times G]$ and $C=Y-[e,e]$. If $\|C\|_w<1/4$, then for the partial sums
--   $$
--   X_k=\sum_{j=0}^k\binom{1/2}{j}C^j,\qquad \binom{\alpha}{j}=\frac{\alpha(\alpha-1)(\alpha-2)\cdots(\alpha-j+1)}{j!},
--   $$
--   we have
--   $$
--   \|Y-X_k^2\|_w\longrightarrow0\qquad(k\to\infty).
--   $$
--   This is the Taylor expansion $\sqrt{1+x}=1+x/2-x^2/8+\cdots$ in the group algebra, used to replace $V_n'$ by the square of a self-adjoint element so that the final operators are positive.
--
--   Differences from the source:
--   - encoding: “for any $k\ge0$ and $X=\sum_{j\le k}\cdots$, $\|Y-X^2\|_w\to0$ as $k\to\infty$” → convergence to $0$ of the sequence $k\mapsto\|Y-X_k^2\|_w$; reason: $X$ depends on $k$; this is the meaning of the limit
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Proposition 4.12, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra

open Filter Topology

namespace QuantumSymmetryBreaking.CycleColoring

/-- Proposition 4.12, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.20 (PDF p.23).
Let `Y ∈ ℂ[G × G]` and `C = Y − [e,e]`. If `‖C‖_w < 1/4`, then with `X_k = ∑_{j=0}^k (1/2 choose j) C^j`
we have `‖Y − X_k^2‖_w → 0` as `k → ∞`. -/
theorem proposition_4_12 (s : ℕ) (Y : Alg s) (hC : algW (Y - br 1 1) < 1 / 4) :
    Tendsto (fun k : ℕ => algW (Y - sqrtPartial (Y - br 1 1) k ^ 2)) atTop (𝓝 0) := by sorry

end QuantumSymmetryBreaking.CycleColoring
