-- Prove2me | Theorems.Thm_SuperlatSVP_Supplement_theorem_3_4
-- name    : SuperlatSVP.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:36:53.599949+00:00
-- url     : https://prove2.me/theorems/543673b1-26f7-4db3-9266-65bbceb0adb8
-- title:
--   Theorem 3.4 — one sample within TV $e^{-\kappa}$ of $D_{L,s}$, any $s>0$, $\kappa\ge n$, in time and space $2^{n/2+\mathrm{polylog}(\kappa)+o(n)}$
-- statement:
--   **Theorem 3.4 (one discrete Gaussian sample by restriction).** There are a randomized program $P$, a function $g$ with $g(n)/n\to0$ and an integer $K$ with the following property. Take any $n\ge1$, any invertible $B\in\mathbb Q^{n\times n}$, any rational $s>0$ and any rational $\kappa\ge n$, and let $\ell$ be the bit length of the input $(n,B,s,\kappa)$. Then on every coin tape $P$ halts within bit time and bit space
--   $$2^{\,n/2+K(\log_2(\kappa+2))^K+g(n)}\,(\ell+1)^K .$$
--   Its output, the coefficient vector of a lattice point of $L(B)=B\mathbb Z^n$, is within total variation distance
--   $$e^{-\kappa}$$
--   of the discrete Gaussian $D_{L(B),s}$.
--
--   The theorem gives an exact-width discrete Gaussian sampler at **every** width $s>0$, with no smoothing condition on $s$, at the cost $2^{n/2+o(n)}$ of a smooth-width sampler. It does so by restricting samples from a random smooth superlattice to $L$.
--
--   **Formalization Note** Costs are bit time and bit space of the published randomized log-cost rational RAM `TwMSOCount.Main`. The output distribution is compared with $D_{L(B),s}$ over all possible output words (`SamplesDGSWithin`).
--
--   Differences from the source:
--   - reading: "runs in time and space 2^{n/2+polylog(κ)+o(n)}" (no machine named; Algorithm 1 uses the external ADRS sampler) → some program on the randomized log-cost RAM halts on every coin tape within bit time and space 2^{n/2+K(log₂(κ+2))^K+g(n)}·(ℓ+1)^K, with P, g, K fixed before the input; reason: the paper fixes no machine, and "on every tape" is the stronger reading. The poly(ℓ) factor is the paper's implicit dependence on the input bit length (p.14) and ADRS's "up to polynomial factors in the input length" (p.19). polylog(κ) is uniform (p.14).
--   - encoding: a basis of L, s > 0, κ ≥ n → an invertible rational B, rational s > 0, rational κ ≥ n, input word (n, B row by row, s, κ), output the integer coefficient vector x of the sample Bx; reason: algorithm inputs and outputs are finite words.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3.1, p.25 (PDF p.25), Theorem 3.4; Algorithm 1, p.25; §2, p.14

import Mathlib
import Definitions.Def_SuperlatSVP_Supplement_SamplesDGSWithin

open Filter

namespace SuperlatSVP.Supplement

/-- Theorem 3.4 (One discrete Gaussian sample in 2^{n/2+o(n)} time). Hhan, Kim, Kim, Laarhoven,
*Superlattice methods for the shortest vector problem and discrete Gaussian sampling*, STOC 2027
submission (manuscript sha256 fcf5b14f…ba), §3.1, p.25 (PDF p.25): "Given a basis of an
n-dimensional lattice L, s > 0, and κ ≥ n, Algorithm 1 runs in time and space
2^{n/2+polylog(κ)+o(n)} and outputs a sample within total variation distance e^{−κ} from DL,s."

**Formalization Note.** One randomized program `P`, one `g` with `g(n)/n → 0` (time and space)
and one exponent `K` are chosen before the dimension and the input; `polylog(κ)` is written
`K·(log₂(κ+2))^K`. For every `n ≥ 1`, every invertible `B ∈ ℚ^{n×n}`, every rational `s > 0` and
every rational `κ ≥ n`, the run on the input word `w` (`n`, `B` row by row, `s`, `κ`) halts on
**every** coin tape within bit time and bit space `2^{n/2+K(log₂(κ+2))^K+g(n)}·(ℓ+1)^K`, `ℓ` the
bit length of `w` (§2, p.14; [ADRS15]'s "up to polynomial factors in the input length", p.19), on
the randomized log-cost RAM `TwMSOCount.Main`, and its output (the coefficient vector `x` of the
sample `Bx`) is within total variation `e^{−κ}` of `D_{L(B),s}` (`SamplesDGSWithin`). The paper's
Algorithm 1 is not formalized; the statement asserts that some program meets its guarantee. -/
theorem theorem_3_4 :
    ∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ),
      Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        ∀ s : ℚ, 0 < s → ∀ κ : ℚ, (n : ℚ) ≤ κ →
          HaltsWithin P (dgsInput B s κ)
              ((2 : ℝ) ^ ((n : ℝ) / 2 + K * Real.logb 2 ((κ : ℝ) + 2) ^ K + g n) *
                ((wordBits (dgsInput B s κ) : ℝ) + 1) ^ K)
              ((2 : ℝ) ^ ((n : ℝ) / 2 + K * Real.logb 2 ((κ : ℝ) + 2) ^ K + g n) *
                ((wordBits (dgsInput B s κ) : ℝ) + 1) ^ K) ∧
            SamplesDGSWithin P (dgsInput B s κ) B (s : ℝ) (Real.exp (-(κ : ℝ))) := by sorry

end SuperlatSVP.Supplement
