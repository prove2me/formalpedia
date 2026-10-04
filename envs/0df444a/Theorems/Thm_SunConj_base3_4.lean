-- Prove2me | Theorems.Thm_SunConj_base3_4
-- name    : SunConj.base3_4
-- status  : Open
-- author  : @williambc
-- created : 2026-10-04T00:27:49.646158+00:00
-- url     : https://prove2.me/theorems/33318fc6-2779-435d-aeba-8210e86f9325
-- title:
--   Base series of Conjecture 3.4: $\frac{\binom{2k}{k}^2\binom{4k}{2k}}{(-12288)^k}(28k+3)=\frac{16}{\sqrt3\,\pi}$
-- statement:
--   # Base series of Conjecture 3.4: $\frac{\binom{2k}{k}^2\binom{4k}{2k}}{(-12288)^k}(28k+3)=\frac{16}{\sqrt3\,\pi}$
--
--   Lean: `SunConj.base3_4` in `lean/Theorems/Thm_SunConj_base3_4.lean`.
--
--   $$\sum_{k=0}^{\infty}\frac{\binom{2k}{k}^2\binom{4k}{2k}}{(-12288)^k}(28k+3)=\frac{16}{\sqrt3\,\pi}.$$
--
--   Proved Ramanujan-type series; Conjecture 3.4 adds harmonic-number weights to its summand.
--
--   Notation: $\binom nk$ is the binomial coefficient; $H_n=\sum_{j=1}^n 1/j$ is the $n$-th harmonic number ($H_0=0$); $G=\sum_{n\ge0}(-1)^n/(2n+1)^2$ is Catalan's constant (Prove2Me's `FCP.Constants.catalanConstant`); $\zeta(3)=\sum_{n\ge1}1/n^3$; $L_{-8}(2)=\sum_{n\ge1}\left(\frac{-8}{n}\right)/n^2$ with the Kronecker symbol $\left(\frac{-8}{n}\right)$ ($=1$ for $n\equiv1,3$, $=-1$ for $n\equiv5,7 \pmod 8$, $=0$ for even $n$); $L_{-3}(2)=\sum_{n\ge0}\bigl(\frac1{(3n+1)^2}-\frac1{(3n+2)^2}\bigr)$. All series are over integers $k\ge0$ and converge absolutely (geometrically); "$\sum a_k=S$" is stated in Lean as `HasSum`, i.e. the series is summable with sum $S$.
--
--   **Status.** Proved in the literature; cited as a foundation (`foundations/SunConj_base3_4.md`), not proved here.
--
--   **Source.** Z.-W. Sun, "Various conjectural series identities", arXiv:2603.29973v3 (13 April 2026), https://arxiv.org/abs/2603.29973, quoted as the known base series of Conjecture 3.4 (original reference to be confirmed by the citation check).
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/a9c54f745fc614e8c91305e866a28985370aef9f/math-problems/statements/SunConj_base3_4.md

import Definitions.Def_SunConj_Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Harmonic.Defs

namespace SunConj

theorem base3_4 :
    HasSum (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) ^ 2 * (Nat.choose (4 * k) (2 * k) : ℝ) / (-12288 : ℝ) ^ k * (28 * (k : ℝ) + 3))
    (16 / (Real.sqrt 3 * Real.pi)) := by sorry

end SunConj
