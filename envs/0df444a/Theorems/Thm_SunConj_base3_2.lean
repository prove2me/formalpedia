-- Prove2me | Theorems.Thm_SunConj_base3_2
-- name    : SunConj.base3_2
-- status  : Open
-- author  : @williambc
-- created : 2026-10-03T22:27:20.459433+00:00
-- url     : https://prove2.me/theorems/1c5a2475-b733-4eca-be5a-3b317758fd44
-- title:
--   Base series of Conjecture 3.2: $\frac{\binom{2k}{k}^2\binom{3k}{k}}{(-12)^{3k}}(51k+7)=\frac{12\sqrt3}{\pi}$
-- statement:
--   # Base series of Conjecture 3.2: $\frac{\binom{2k}{k}^2\binom{3k}{k}}{(-12)^{3k}}(51k+7)=\frac{12\sqrt3}{\pi}$
--
--   Lean: `SunConj.base3_2` in `lean/Theorems/Thm_SunConj_base3_2.lean`.
--
--   $$\sum_{k=0}^{\infty}\frac{\binom{2k}{k}^2\binom{3k}{k}}{(-12)^{3k}}(51k+7)=\frac{12\sqrt3}{\pi}.$$
--
--   Proved Ramanujan-type series; Conjecture 3.2 adds harmonic-number weights to its summand.
--
--   Notation: $\binom nk$ is the binomial coefficient; $H_n=\sum_{j=1}^n 1/j$ is the $n$-th harmonic number ($H_0=0$); $G=\sum_{n\ge0}(-1)^n/(2n+1)^2$ is Catalan's constant (Prove2Me's `FCP.Constants.catalanConstant`); $\zeta(3)=\sum_{n\ge1}1/n^3$; $L_{-8}(2)=\sum_{n\ge1}\left(\frac{-8}{n}\right)/n^2$ with the Kronecker symbol $\left(\frac{-8}{n}\right)$ ($=1$ for $n\equiv1,3$, $=-1$ for $n\equiv5,7 \pmod 8$, $=0$ for even $n$); $L_{-3}(2)=\sum_{n\ge0}\bigl(\frac1{(3n+1)^2}-\frac1{(3n+2)^2}\bigr)$. All series are over integers $k\ge0$ and converge absolutely (geometrically); "$\sum a_k=S$" is stated in Lean as `HasSum`, i.e. the series is summable with sum $S$.
--
--   **Status.** Proved in the literature; cited as a foundation (`foundations/SunConj_base3_2.md`), not proved here.
--
--   **Source.** Z.-W. Sun, "Various conjectural series identities", arXiv:2603.29973v3 (13 April 2026), https://arxiv.org/abs/2603.29973, quoted as the known base series of Conjecture 3.2 (original reference to be confirmed by the citation check).
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/162c03a7baa1a4605a86d0ac78a1ec3d39db64d5/math-problems/statements/SunConj_base3_2.md

import Definitions.Def_SunConj_Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Harmonic.Defs

namespace SunConj

theorem base3_2 :
    HasSum (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) ^ 2 * (Nat.choose (3 * k) k : ℝ) / (-12 : ℝ) ^ (3 * k) * (51 * (k : ℝ) + 7))
    (12 * Real.sqrt 3 / Real.pi) := by sorry

end SunConj
