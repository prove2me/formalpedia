-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_1
-- name    : QaryCVP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:53.900837+00:00
-- url     : https://prove2.me/theorems/ddf49b40-9bd8-4e15-bae8-3242de70ff37
-- title:
--   Lemma 4.1 — exact dynamic programming over $(\mathbb Z/q\mathbb Z)^m$ in time $nq^{m+1}\,\mathrm{poly}$
-- statement:
--   There is a deterministic program $A$ such that for integers $q\ge2$, $m\ge1$, $n\ge1$, every $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ and $y\in\mathbb Q^n$, $A(H,y)$ returns a point of $\Lambda$ closest to $y$, with
--
--   $$\text{time } nq^{m+1}\,\mathrm{poly},\qquad\text{space } nq^m\,\mathrm{poly}.$$
--
--   In terms of the density $\delta=m\log_2q/n$, these are at most $2^{2\delta n}\,\mathrm{poly}$ and $2^{\delta n}\,\mathrm{poly}$.
--
--   It handles the densities $\delta\le1/8$ and every fallback of the $\gamma$-CVP algorithm exactly.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - encoding: deterministic procedure → the program's run is the same on every coin tape; reason: determinism on the randomized machine
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.1, p.35

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Lemma 4.1** (exact dynamic programming over `(Z/qZ)^m`). Kim, Kwon, Lee, Lee, STOC 2027
submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.1, p.35.

There is a deterministic program `A` and a degree `K` such that, for integers `q ≥ 2`, `m ≥ 1`,
`n ≥ 1`, every `H ∈ (Z/qZ)^{m×n}` and `y ∈ Qⁿ`, `A(H, y)` returns a point of `Λ` closest to `y`, in
bit time `n q^{m+1} · poly` and bit space `n q^m · poly`; in terms of `δ = m log₂ q / n` these are at
most `2^{2δn} poly` and `2^{δn} poly`. Here `poly` is `(ℓ + 1)^K`, `ℓ` the binary input length.

**Formalization Note.** Deterministic = the run is the same on every coin tape. -/
theorem lemma_4_1 :
    ∃ (A : Program) (K : ℕ), ∀ q m n : ℕ, 2 ≤ q → 1 ≤ m → 1 ≤ n →
      ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ),
        DetOn A (encInst H y) ∧
        (∀ ω : ℕ → Bool, ∃ x : Fin n → ℤ, IsClosest H y x ∧
          callOutput A (Config.init (encInst H y)) ω = some (encZVec x)) ∧
        RunsWithin A (encInst H y)
          ((n : ℝ) * (q : ℝ) ^ (m + 1) * polyF K (encInst H y))
          ((n : ℝ) * (q : ℝ) ^ m * polyF K (encInst H y)) ∧
        RunsWithin A (encInst H y)
          ((2 : ℝ) ^ (2 * density q m n * n) * polyF K (encInst H y))
          ((2 : ℝ) ^ (density q m n * n) * polyF K (encInst H y)) := by sorry

end QaryCVP
