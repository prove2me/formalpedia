-- Prove2me | Theorems.Thm_SuperlatSVP_Supplement_theorem_1_9
-- name    : SuperlatSVP.Supplement.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:38:31.341208+00:00
-- url     : https://prove2.me/theorems/eb99d26c-82f8-4f96-8385-edd3f5aa7774
-- title:
--   Theorem 1.9 — discrete Gaussian sampling at every width within TV $2^{-\kappa}$ in time and space $(3/2)^{n/2+o(n)}\mathrm{poly}(\kappa)$
-- statement:
--   **Theorem 1.9 (discrete Gaussian sampling).** There are a randomized program $P$, a function $g$ with $g(n)/n\to0$ and an integer $K$ with the following property. Take any $n\ge1$, any invertible $B\in\mathbb Q^{n\times n}$, any rational squared width $s^2>0$ and any integer $\kappa\ge1$, and let $\ell$ be the bit length of the input $(n,B,s^2,\kappa)$. Then on every coin tape $P$ halts within bit time and bit space
--   $$\Big(\frac32\Big)^{n/2+g(n)}(\kappa+1)^K(\ell+1)^K .$$
--   It outputs the coefficient vector of a point $x\in L(B)$ whose distribution is within total variation distance
--   $$2^{-\kappa}$$
--   of $D_{L(B),s}$, where $s=\sqrt{s^2}$.
--
--   The width is arbitrary, so this is exact discrete Gaussian sampling on worst-case lattices in time $2^{0.2924\ldots n+o(n)}$, below the $2^{n/2}$ of smooth-width samplers.
--
--   **Formalization Note** Costs are bit time and bit space of the published randomized log-cost rational RAM `TwMSOCount.Main`. The output distribution is compared with $D_{L(B),s}$ over all possible output words (`SamplesDGSWithin`).
--
--   Differences from the source:
--   - reading: a "bounded randomized (classical) algorithm" with T, S = (3/2)^{n/2+o(n)}poly(κ) (no machine named) → some program on the randomized log-cost RAM halts on every coin tape within bit time and space (3/2)^{n/2+g(n)}(κ+1)^K(ℓ+1)^K, with P, g, K fixed before the input; reason: "bounded" means a worst-case bound on every tape. The poly(ℓ) factor is the paper's implicit dependence on the input bit length (p.14); Algorithm 6 tries K = n⌈log₂(2+s²‖B⁻¹‖²_F)⌉ mass bounds (p.57), polynomially many in ℓ. The o(n) and poly(κ) are uniform (p.14; proof p.58).
--   - encoding: an input lattice L, s² > 0, κ ≥ 1 → an invertible rational B, rational s² > 0, integer κ ≥ 1 (Algorithm 6's input, p.55), input word (n, B row by row, s², κ), output the integer coefficient vector of the point; reason: algorithm inputs and outputs are finite words.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §5.2, p.57 (PDF p.57), Theorem 1.9 (restated; first stated p.6), eq. (1.14); Algorithm 6, p.55; Lemma 5.3, p.57; proof p.58

import Mathlib
import Definitions.Def_SuperlatSVP_Supplement_SamplesDGSWithin

open Filter

namespace SuperlatSVP.Supplement

/-- Theorem 1.9 (Discrete Gaussian sampling, restated). Hhan, Kim, Kim, Laarhoven, *Superlattice
methods for the shortest vector problem and discrete Gaussian sampling*, STOC 2027 submission
(manuscript sha256 fcf5b14f…ba), §5.2, p.57 (PDF p.57; first stated p.6): "For an input lattice L
of rank n, a squared Gaussian width s² > 0 and an accuracy parameter κ ≥ 1, a bounded randomized
(classical) algorithm outputs a point x ∈ L within total variation 2^{−κ} of DL,s in time T and
space S satisfying T = (3/2)^{n/2+o(n)} poly(κ), S = (3/2)^{n/2+o(n)} poly(κ). (1.14)"
Algorithm 6, p.55: "Input: a rational basis B, rational s² > 0, and integer κ ≥ 1."

**Formalization Note.** One randomized program `P`, one `g` with `g(n)/n → 0` (time and space)
and one exponent `K` are chosen before the dimension and the input; `poly(κ)` is `(κ+1)^K`. For
every `n ≥ 1`, every invertible `B ∈ ℚ^{n×n}`, every rational `s² > 0` and every integer `κ ≥ 1`,
the run on the input word `w` (`n`, `B` row by row, `s²`, `κ`) halts on **every** coin tape
("bounded") within bit time and bit space `(3/2)^{n/2+g(n)}·(κ+1)^K·(ℓ+1)^K`, `ℓ` the bit length
of `w` (§2, p.14), on the randomized log-cost RAM `TwMSOCount.Main`, and its output (the
coefficient vector `x` of the point `Bx`) is within total variation `2^{−κ}` of `D_{L(B),s}`,
`s = √(s²)` (`SamplesDGSWithin`). No condition is placed on `s` relative to the smoothing
parameter. -/
theorem theorem_1_9 :
    ∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ),
      Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        ∀ s2 : ℚ, 0 < s2 → ∀ κ : ℕ, 1 ≤ κ →
          HaltsWithin P (dgsInput B s2 κ)
              ((3 / 2 : ℝ) ^ ((n : ℝ) / 2 + g n) * ((κ : ℝ) + 1) ^ K *
                ((wordBits (dgsInput B s2 κ) : ℝ) + 1) ^ K)
              ((3 / 2 : ℝ) ^ ((n : ℝ) / 2 + g n) * ((κ : ℝ) + 1) ^ K *
                ((wordBits (dgsInput B s2 κ) : ℝ) + 1) ^ K) ∧
            SamplesDGSWithin P (dgsInput B s2 κ) B (Real.sqrt (s2 : ℝ))
              ((2 : ℝ) ^ (-(κ : ℝ))) := by sorry

end SuperlatSVP.Supplement
