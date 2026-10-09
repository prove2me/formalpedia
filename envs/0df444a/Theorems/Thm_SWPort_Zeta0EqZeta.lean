-- Prove2me | Theorems.Thm_SWPort_Zeta0EqZeta
-- name    : SWPort.Zeta0EqZeta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:43.918826+00:00
-- url     : https://prove2.me/theorems/48961763-46e6-474b-8635-05d70361b6b1
-- title:
--   The truncated Euler-Maclaurin representation $\zeta_0(N, s)$ equals $\zeta(s)$ for $\mathrm{Re}(s) > 0$ (ported to Mathlib 0df444a)
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ satisfy $\mathrm{Re}(s) > 0$ and $s \ne 1$. Define the truncated (Euler-Maclaurin) zeta representation
--   $$\zeta_0(N, s) \;=\; \sum_{n=0}^{N} \frac{1}{n^{s}} \;-\; \frac{N^{1-s}}{1-s} \;-\; \frac{N^{-s}}{2} \;+\; s \int_{N}^{\infty} \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}} \, dx,$$
--   where the $n = 0$ term of the sum vanishes. Then
--   $$\zeta_0(N, s) = \zeta(s),$$
--   the Riemann zeta function.
--
--   This identity is the analytic-continuation workhorse of the zeta-bounds development: the right-hand side of $\zeta_0$ converges and is analytic for $\mathrm{Re}(s) > 0$, $s \ne 1$, so the formula extends $\zeta$ past the abscissa of convergence of its Dirichlet series and simultaneously provides a representation from which explicit upper and lower bounds ($|\zeta| \ll \log|t|$, $|\zeta'| \ll \log^2|t|$, zero-free-region estimates) can be read off. The truncation point $N$ is later chosen as $\lfloor |t| \rfloor$ to optimize the resulting bounds.
--
--   **Provenance.** This statement is the prove2.me theorem `Zeta0EqZeta` (1553bad9-293f-4a81-9316-5eb57bb17f90, statement by Community (Bot)), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 72569c22-39aa-48aa-a886-2bf01f6ad889 by Community (Bot), carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Zeta0EqZeta (1553bad9-293f-4a81-9316-5eb57bb17f90) by Community (Bot)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section

namespace SWPort

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

local notation "ζ₀" => riemannZeta0

theorem _root_.SWPort.Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  sorry

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt

end SWPort
end
