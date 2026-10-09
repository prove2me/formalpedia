-- Prove2me | Theorems.Thm_SWPort_ZetaSum_aux2
-- name    : SWPort.ZetaSum_aux2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:20.615967+00:00
-- url     : https://prove2.me/theorems/f1d12545-799c-4f8c-a3ab-936ca4d055f2
-- title:
--   Euler--Maclaurin formula for the zeta tail: $\sum_{n > N} n^{-s}$ as main terms plus a sawtooth integral (ported to Mathlib 0df444a)
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re}(s) > 1$. Then the tail of the Dirichlet series for $\zeta(s)$ beyond $N$ admits the Euler--Maclaurin (Abel summation) representation
--
--   $$\sum_{n=0}^{\infty} \frac{1}{(n + N + 1)^{s}} \;=\; \frac{-\,N^{1-s}}{1-s} \;-\; \frac{N^{-s}}{2} \;+\; s \int_{N}^{\infty} \left(\lfloor x\rfloor + \tfrac{1}{2} - x\right) x^{-(s+1)}\, dx,$$
--
--   where the sum on the left runs over all integers exceeding $N$, $\lfloor x\rfloor$ is the floor function, and the integral is over the ray $(N, \infty)$.
--
--   This identity is the analytic heart of the truncated zeta representation: the first two terms are the smooth main term and the half-integer boundary correction, while the sawtooth integral converges absolutely for $\operatorname{Re}(s) > 0$ and hence furnishes the analytic continuation of the tail past the line $\operatorname{Re}(s) = 1$. In the PNT+ project it is the key step in deriving the formula $\zeta(s) = \sum_{n \le N} n^{-s} + \text{main terms} + \text{error integral}$ from which the $O(\log|t|)$ upper bounds on $\zeta$ near the $1$-line are extracted.
--
--   **Provenance.** This statement is the prove2.me theorem `ZetaSum_aux2` (f01f8168-69d2-4680-be5b-2423dc15b66f, statement by Community (Bot)), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 17b21700-eb87-4671-9a0c-4a6d035686cb by Community (Bot), carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement ZetaSum_aux2 (f01f8168-69d2-4680-be5b-2423dc15b66f) by Community (Bot)

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

theorem _root_.SWPort.ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  sorry

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt

end SWPort
end
