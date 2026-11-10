-- Prove2me | Theorems.Thm_SuperlatSVP_corollary_1_5
-- name    : SuperlatSVP.corollary_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:29.563623+00:00
-- url     : https://prove2.me/theorems/3bc2823f-588b-40ad-a3e9-e58da1e7c232
-- title:
--   Corollary 1.5 (1.8), classical clause — worst-case exact SVP in time $(3/(\sqrt{6\pi/e}-1))^{n/2+o(n)}$ and space $(8e/(3\pi))^{n/4+o(n)}$
-- statement:
--   There are:
--
--   - a randomized program $P$;
--   - a function $g$ with $g(n)/n\to0$;
--   - an exponent $K$;
--
--   such that for every dimension $n\ge1$ and every invertible basis $B\in\mathbb Q^{n\times n}$, $P$ outputs, with probability at least $2/3$, the coefficient vector of a shortest nonzero vector of the lattice $L(B)$. On every coin tape it halts within
--   $$\text{time }T=\left(\frac{3}{\sqrt{6\pi/e}-1}\right)^{n/2+g(n)}(\ell+1)^K=2^{0.4385\ldots n+o(n)}(\ell+1)^K$$
--   and
--   $$\text{space }S=\left(\frac{8e}{3\pi}\right)^{n/4+g(n)}(\ell+1)^K=2^{0.3015\ldots n+o(n)}(\ell+1)^K,$$
--   where $\ell$ is the bit length of the input.
--
--   This is the paper's headline: exact SVP on every lattice below the $2^{n/2}$ time barrier. It is Theorem 1.4 with the worst-case exponent $\beta=\tfrac12\log_2(2e/\pi)$ of Proposition 1.3 and the parameter $\alpha=\beta/2+\tfrac14\log_2(4/3)$.
--
--   **Formalization Note** $P$, $g$ and $K$ are fixed before the dimension and the basis. Costs are bit time and bit space of the randomized log-cost RAM `TwMSOCount.Main`. The bound holds on every coin tape, not in expectation.
--
--   Differences from the source:
--   - reading: "time" and "space" of an algorithm (no machine named) → bit time and bit space of the randomized log-cost rational RAM TwMSOCount.Main on every coin tape, times (ℓ+1)^K for the input length ℓ; reason: exact exponents need a random-access machine; "on every tape" is the stronger reading and the proof caps the work (p.44); the poly(ℓ) factor is the source's implicit dependence on the bit length (p.14)
--   - encoding: an input lattice given by a basis → an invertible rational basis B, input word n then B row by row, output the integer coefficient vector of a shortest nonzero vector; reason: algorithm inputs are finite words; real bases are not inputs
--   - reading: Corollary 1.5 states a classical bound (1.8) and a "Quantumly" bound (1.9) with coherent indexed access to stored classical arrays → this item is the classical clause (1.8); reason: (1.9) is a separate result in a quantum-RAM model, proved by the separate Theorem 4.19 and not used by (1.8); no quantum machine model is available
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §1.2.3, p.5 (PDF p.5), Corollary 1.5, eq. (1.8); success probability from Theorem 1.4, p.5; proof §4.5, p.49

import Mathlib
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open Filter

namespace SuperlatSVP

/-- Corollary 1.5 (Minimum time), classical clause. Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §1.2.3, p.5 (PDF p.5): "Setting
β = 1/2 log2(2e/π) and α = β/2 + 1/4 log2(4/3), SVP can be solved on every input lattice in time and
space T = (3/(√(6π/e) − 1))^{n/2+o(n)} = 2^{0.4385...n+o(n)}, S = (8e/(3π))^{n/4+o(n)} = 2^{0.3015...n+o(n)}.
(1.8)" The success probability is that of Theorem 1.4 (p.5): "exact SVP has an algorithm with success
probability at least 2/3".

**Formalization Note.** One randomized program `P`, one `g` with `g(n)/n → 0` (time and space) and
one exponent `K`, all chosen before the dimension and the basis. For every `n ≥ 1` and every
invertible `B ∈ ℚ^{n×n}` (input word: `n`, then `B` row by row), on every coin tape the run halts
within bit time `(3/(√(6π/e) − 1))^{n/2+g(n)}·(ℓ+1)^K` and bit space `(8e/(3π))^{n/4+g(n)}·(ℓ+1)^K`
(`ℓ` the input bit length) on the randomized log-cost RAM `TwMSOCount.Main`, and with probability
at least `2/3` it outputs the coefficient vector of a shortest nonzero vector of `L(B)`
(`SolvesSVPWithin`). The quantum clause (1.9) is not part of this item. -/
theorem corollary_1_5 :
    ∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ),
      Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        SolvesSVPWithin P K
          ((3 / (Real.sqrt (6 * Real.pi / Real.exp 1) - 1)) ^ ((n : ℝ) / 2 + g n))
          ((8 * Real.exp 1 / (3 * Real.pi)) ^ ((n : ℝ) / 4 + g n)) B := by sorry

end SuperlatSVP
