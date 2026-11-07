-- Prove2me | Theorems.Thm_PRUPermLayer_fact_2_3
-- name    : PRUPermLayer.fact_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:19.764217+00:00
-- url     : https://prove2.me/theorems/ee30e8de-3514-4fae-b63f-52cdbc921823
-- title:
--   Fact 2.3 — $c(\mathrm{Dist}_{N,t},\mathrm{NoPlus}_{N,t})^2 \le \gamma_t$ for $2 \le t \le N/2$
-- statement:
--   Let $N = 2^n$ and $\gamma_t = t(t-1)/(N-t+1)$. For every integer $t$ with $2 \le t \le N/2$,
--   $$
--   c\big(\mathrm{Dist}_{N,t}, \mathrm{NoPlus}_{N,t}\big)^2 \le \gamma_t ,
--   $$
--   where $c$ is the Friedrichs cosine.
--
--   The paper imports this from [FLM+26, Lemma 7.15] and checks on the same page that the proof gives the range $2 \le t \le N/2$. It controls the overlap of the two subspaces outside their intersection, and so the cost of intersecting them.
--
--   Differences from the source:
--   - encoding: $t \le N/2$ → $2t \le 2^n$ in $\mathbb N$; reason: equivalent for integers
--   - encoding: $N = 2^n$ with $[N] \cong \{0,1\}^n$ → labels in $\{0,\dots,2^n-1\}$ read as $n$-bit strings, most significant bit first; reason: Lean convention; same instances
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PRUPermLayer_friedrichsCos
import Definitions.Def_PRUPermLayer_distSub
import Definitions.Def_PRUPermLayer_noPlusSub
import Definitions.Def_PRUPermLayer_gammaT
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Fact 2.3** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.3, p.10 (PDF p.12), quoting [FLM+26, Lemma 7.15] with the range
`2 ≤ t ≤ N/2` checked on the same page). Let `N = 2ⁿ` and `γ_t = t(t − 1)/(N − t + 1)`. For
`2 ≤ t ≤ N/2`, `c(Dist_{N,t}, NoPlus_{N,t})² ≤ γ_t`.

**Formalization Note** `t ≤ N/2` is `2 * t ≤ 2 ^ n` in `ℕ` (equivalent). -/
theorem fact_2_3 (n t : ℕ) (ht : 2 ≤ t) (htN : 2 * t ≤ 2 ^ n) :
    friedrichsCos (distSub (2 ^ n) t) (noPlusSub (2 ^ n) t) ^ 2 ≤ gammaT (2 ^ n) t := by sorry

end PRUPermLayer
