-- Prove2me | Theorems.Thm_SparseHistComm_theorem_3
-- name    : SparseHistComm.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:41:26.757322+00:00
-- url     : https://prove2.me/theorems/292f6627-77a6-4845-9e70-a49247cc197d
-- title:
--   Theorem 3 (Homogeneous communication characterization): $C_{\mathrm{hom}}(D,\delta) = \Lambda_{n,k,D}(\delta)\log d + o(\log d)$
-- statement:
--   Fix $n \ge 1$, $k \ge 1$, $D$ and $\delta$ with $0 \le D < k$ and $0 \le \delta < 1$, and let $C_{\mathrm{hom}}(D,\delta)$ be the smallest worst-case expected total message length of a $(D,\delta)$-accurate homogeneous protocol for $n$ users holding $k$-sparse binary vectors in $\{0,1\}^d$. Then:
--
--   1. for all sufficiently large $d$,
--   $$
--   C_{\mathrm{hom}}(D,\delta) \ \ge\ \Lambda_{n,k,D}\Big(\delta + \frac{n^2(k + D)}{(\lfloor nD\rfloor + 1 - nD)\log d}\Big)\log d - O(\log\log d); \tag{21}
--   $$
--   2. together with (13),
--   $$
--   C_{\mathrm{hom}}(D,\delta) = \Lambda_{n,k,D}(\delta)\log d + o(\log d), \qquad d \to \infty . \tag{22}
--   $$
--
--   Here $\log$ is base 2 and $\Lambda_{n,k,D}(\delta)$ is the homogeneous coefficient (12): the minimal expected total covering level of a randomized covering scheme in which all users draw their levels i.i.d. from a common publicly randomized law. The theorem identifies the exact first-order communication cost of homogeneous encoders, which exceeds the heterogeneous cost $(1-\delta)(nk - \lfloor nD\rfloor)\log d$ whenever $\lfloor nD\rfloor \ne n\lfloor D\rfloor$.
--
--   Differences from the source:
--   - reading: "for all sufficiently large d, … − O(log log d)" for fixed n, k, D, δ → ∃ C ∃ d₀ ∀ d ≥ d₀, with C independent of d and of the protocol; reason: the standard meaning of the asymptotic bound for fixed parameters
--   - reading: "C_hom(D, δ) = Λ_{n,k,D}(δ) log d + o(log d), d → ∞" → C_hom is finite for all large d, and (C_hom − Λ log d)/log d → 0 along d → ∞; reason: the equality with a real quantity presupposes finiteness; o(log d) is the ratio limit
--   - encoding: protocols with any public randomness R, channels into {0,1}*, estimate from the messages and R → Protocol n d (Ω : Type with any probability measure, PMF (List Bool) channels and decoder measurable in r, decoder deterministic given (r, m)); reason: every probability and expectation of the paper presupposes measurability in r; private server randomness can be moved into R
--   - encoding: binary vectors xᵢ ∈ {0,1}^d with ‖xᵢ‖₀ ≤ k → supports Finset (Fin d) with card ≤ k; reason: bijection
--   - encoding: Λ_{n,k,D} as a min over (L(R), p_R) → sInf over probability laws ν of p_R on the simplex; reason: objective and constraint depend only on the law of p_R; the minimum is attained (Lemma 3), so the value agrees
--   - encoding: real inequality (21) → ENNReal.ofReal (real side) ≤ C_hom in ℝ≥0∞; reason: C_hom ≥ 0, so equivalent
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 3, Eq. (21)–(22), p.9

import Mathlib
import Definitions.Def_SparseHistComm_Chom
import Definitions.Def_SparseHistComm_Lambda

namespace SparseHistComm

/-- **Theorem 3 (Homogeneous communication characterization)** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.9). Fix
`n, k, D, δ` with `0 ≤ D < k` and `0 ≤ δ < 1`. For all sufficiently large `d`,
`C_hom(D, δ) ≥ Λ_{n,k,D}(δ + n²(k + D)/((⌊nD⌋ + 1 − nD) log d)) log d − O(log log d)` (21), and
together with (13), `C_hom(D, δ) = Λ_{n,k,D}(δ) log d + o(log d)` as `d → ∞` (22).

**Formalization Note**
1. `−O(log log d)` for fixed `n, k, D, δ` is `∃ C ∃ d₀` (independent of `d` and of the protocol);
   the real right side is embedded by `ENNReal.ofReal`, which is equivalent because `C_hom ≥ 0`.
2. `= Λ log d + o(log d)` is: `C_hom` is finite for all large `d`, and
   `(C_hom − Λ log d)/log d → 0`.
3. `log` is `Real.logb 2` (p.3); `n ≥ 1`, `k ≥ 1` are the paper's standing assumptions (p.2);
   `k ≤ d` and `d ≥ 2` hold for large `d`. -/
theorem theorem_3 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (D δ : ℝ) (hD0 : 0 ≤ D) (hDk : D < k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∃ C : ℝ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ENNReal.ofReal (Lambda n k D (δ + (n : ℝ) ^ 2 * (k + D) /
          (((⌊(n : ℝ) * D⌋ : ℝ) + 1 - n * D) * Real.logb 2 d)) * Real.logb 2 d
        - C * Real.logb 2 (Real.logb 2 d)) ≤ Chom n k d D δ) ∧
    ((∀ᶠ d in Filter.atTop, Chom n k d D δ ≠ ⊤) ∧
      Filter.Tendsto (fun d : ℕ => ((Chom n k d D δ).toReal - Lambda n k D δ * Real.logb 2 d) /
        Real.logb 2 d) Filter.atTop (nhds 0)) := by sorry

end SparseHistComm
