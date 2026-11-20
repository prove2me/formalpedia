-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_Supplement_theorem_9
-- name    : SpreadMatchCircuit.Matching.Supplement.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:34:54.800004+00:00
-- url     : https://prove2.me/theorems/477057be-99a3-49b8-8fe9-2b9e5eecdb1d
-- title:
--   Theorem 9 — The polynomial-image function $F_{k,d}$ needs monotone circuits of size $\exp(\Omega(\min\{d,n/k\}))$
-- statement:
--   There are universal constants $\eta>0$ and $c>0$ such that the following holds. Let $n$ be a prime, and let $k\ge1$ and $d\ge0$ be integers with
--   $$kd\le \eta n\qquad\text{and}\qquad 3d\log n\le k .$$
--   Let $F_{k,d}$ be the Boolean function on the $n$ variables $x_i$, $i\in\mathbb F_n$,
--   $$F_{k,d}(x)=\bigvee_{\substack{w\in D_d\\ |w([k])|\ge k/2}}\ \bigwedge_{i\in w([k])}x_i ,$$
--   where $D_d$ is the set of univariate polynomials of degree $d$ over $\mathbb F_n$ and $w([k])=\{w(1),\dots,w(k)\}$. Every monotone Boolean circuit that computes $F_{k,d}$ on every input has size
--   $$\operatorname{size}(C)\ \ge\ \exp\bigl(c\cdot\min\{d,\,n/k\}\bigr).$$
--
--   The circuits are arbitrary monotone circuits with binary AND and OR gates and unbounded fan-out. With $k=\sqrt n$ and $d=k/(3\log n)$ the function lies in NP and the bound is $\exp(\Omega(\sqrt n/\log n))$. This is a companion result of the mission and is not used in the proof of the matching lower bound.
--
--   **Formalization Note** $\log$ is the natural logarithm. $\mathbb F_n$ is `ZMod n` with `n.Prime`, and the variables are indexed by its elements. "Degree $d$" means degree exactly $d$, so the zero polynomial is excluded. The constants $\eta$ and $c$ are chosen before $n,k,d$ and the circuit. The case $d=0$ is included; there the bound reads $\operatorname{size}(C)\ge1$. The size of a circuit counts all of its nodes, input nodes included.
--
--   Differences from the source:
--   - reading: log unspecified → natural logarithm; reason: the coefficient 3 is kept, and since ln n ≤ log₂ n the hypothesis 3d ln n ≤ k admits every instance of the binary-log reading
--   - encoding: the prime field F_n and its n Boolean coordinates → ZMod n with the hypothesis n.Prime, variables indexed by ZMod n; reason: same field, same variables
--   - reading: polynomials of degree d → polynomials with degree exactly d (nonzero leading coefficient); reason: literal meaning of "degree d"; it excludes the zero polynomial at d = 0
--   - encoding: [k] = {1, …, k} and |w([k])| ≥ k/2 → the casts of 1, …, k into ZMod n, image as a Finset, and k ≤ 2·|w([k])|; reason: same set and same condition
--   - encoding: k implicitly positive (n/k) → 1 ≤ k; reason: excludes only the undefined quotient n/0
--   - encoding: requires monotone circuits of size exp(Ω(min{d, n/k})) → there is an absolute c > 0, chosen before n, k, d and C, such that every circuit agreeing with F_{k,d} on every assignment has C.size ≥ exp(c·min{d, n/k}); reason: the asymptotic exponent is read with a uniform constant and no prefactor
--   - encoding: circuit size → number of nodes of the published monotone circuit model, input nodes included; reason: the mission's circuit model counts input gates as the source does on p. 11
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 5, Theorem 9; definition of D_d and F_{k,d} p. 5 (n prime); proof §5, pp. 17–20

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_PolyImage

namespace SpreadMatchCircuit.Matching.Supplement

/-- Theorem 9, p. 5: for prime `n`, if `kd ≤ ηn` and `3d log n ≤ k`, every monotone circuit
computing `F_{k,d}` exactly has size at least `exp(c · min{d, n/k})`. The constants `η, c` are
absolute and precede every parameter; `log` is the natural logarithm. -/
theorem theorem_9 :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k d : ℕ), n.Prime → 1 ≤ k →
        (k : ℝ) * (d : ℝ) ≤ η * (n : ℝ) → 3 * (d : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) →
        ∀ C : MonotoneCircuit (ZMod n), (∀ x : ZMod n → Bool, C.eval x = true ↔ PolyImageFun n k d x) →
          Real.exp (c * min (d : ℝ) ((n : ℝ) / (k : ℝ))) ≤ (C.size : ℝ) := by sorry

end SpreadMatchCircuit.Matching.Supplement
