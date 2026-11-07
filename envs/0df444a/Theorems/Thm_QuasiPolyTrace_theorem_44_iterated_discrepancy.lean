-- Prove2me | Theorems.Thm_QuasiPolyTrace_theorem_44_iterated_discrepancy
-- name    : QuasiPolyTrace.theorem_44_iterated_discrepancy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:06.182463+00:00
-- url     : https://prove2.me/theorems/fce0f0e4-7346-4d63-8977-2a8b75afad29
-- title:
--   Proof of Theorem 44, iteration — a discrepancy $e^{-p^{-7/3}(\log_2 n)^c}$ on the whole strings
-- statement:
--   There is a universal $c>0$ such that for every $p\in(0,1]$, every $n\ge3$ and all $x\ne y$ in $\{0,1\}^n$ there are a window start $i\le1$, a retention probability $P\in(0,p]$, a statistic $S$ of order at most $3^b$, where $b=\lceil\log_{1.1}\log_2n\rceil$, and an offset $\ell$ with
--
--   $$
--   \big|x^{(S+\ell)}_{[i:n],P}-y^{(S+\ell)}_{[i:n],P}\big|\ \ge\ e^{-p^{-7/3}(\log_2 n)^c} .
--   $$
--
--   The window $x_{[i:n]}$ is $x$ preceded by $1-i$ known zeros. This is the outcome of at most $b$ applications of Proposition 37 started from Lemma 43, stopped once the window reaches the start of the string; the discrepancy $\tau_{\mathrm{base}}^{C^b}$ is bounded below as on p.44.
--
--   Differences from the source:
--   - reading: |x^{(S+ℓ)}_{[d−R−R′:n],P} − y^{(S+ℓ)}_{[d−R−R′:n],P}| ≥ τ_base^{C^b}, P bounded by p → ≥ e^{−p^{−7/3}(log₂ n)^c} for a universal c, n ≥ 3, window start i ≤ 1, 0 < P ≤ p; reason: p.44 bounds τ_base^{C^b} below by this for n ≥ 3 ("we can bound all the constant and constant-to-the-b terms in the exponent by (log_2 n)^c"); the iteration stops when the window start is ≤ 1 (p.43)
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.42–44 (b := ⌈log_{1.1} log_2 n⌉, p.42; "After b iterations…", p.43; the bound by (log_2 n)^c for n ≥ 3, p.44)

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_shift
import Definitions.Def_QuasiPolyTrace_window

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Proof of Theorem 44, iteration step (a quasipolynomially large discrepancy on the whole strings).**
Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.42–44. With "b := ⌈log_{1.1} log_2 n⌉" (p.42) and the iteration of
Proposition 37 from the base case Lemma 43 "stopping when the location d−2R becomes ≤ 1" (p.43): "After b
iterations, we thus conclude that there is some offset ℓ and statistic S of order ≤ 3^b such that for
retention probability P bounded by the retention probability of the actual channel p, the discrepancy is
bounded as |x^{(S+ℓ)}_{[d−R−R′:n],P} − y^{(S+ℓ)}_{[d−R−R′:n],P}| ≥ τ_base^{C^b}" (p.43), and (p.44) "for
n ≥ 3 we can upper bound any constant to the b power by an appropriate constant power of log_2 n, and thus
we can bound all the constant and constant-to-the-b terms in the exponent by (log_2 n)^c for some c,
leading to our bound of e^{p^{−7/3}(log_2 n)^c}."

Statement: there is a universal `c > 0` such that for every retention probability `p ∈ (0, 1]`, every
`n ≥ 3` and every two distinct `n`-bit strings `x ≠ y`, there are a window start `i ≤ 1` (the location
`d − R − R′` after the last iteration), a retention probability `P ∈ (0, p]`, a statistic `S` of order at
most `3^b` and an offset `ℓ` with
`|x^{(S+ℓ)}_{[i:n],P} − y^{(S+ℓ)}_{[i:n],P}| ≥ e^{−p^{−7/3}(log_2 n)^c}`.

**Formalization Note.**
* The lower bound `τ_base^{C^b}` is written after the parameter arithmetic of p.44
  (`τ_base ≥ min(1/C′, e^{−C″ 3^{(7/3)b} max(4^{7/3}, p^{−7/3})})`, `b = ⌈log_{1.1} log_2 n⌉`) in the theorem's
  own form `e^{−p^{−7/3}(log_2 n)^c}`, as the proof does.
* The window starts at `i ≤ 1` and is zero-padded on the left (`window`), the convention of p.42.
* `b = ⌈log_{1.1}(log_2 n)⌉` is the natural-number ceiling; `log_2` is `Real.logb 2`. -/
theorem theorem_44_iterated_discrepancy :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ n : ℕ, 3 ≤ n → ∀ x y : Word n, x ≠ y →
      ∃ i : ℤ, i ≤ 1 ∧ ∃ P : ℝ, 0 < P ∧ P ≤ p ∧
      ∃ (S : Finset ℤ) (ℓ : ℤ), S.card ≤ 3 ^ ⌈Real.logb 1.1 (Real.logb 2 n)⌉₊ ∧
        Real.exp (-(p ^ (-(7 / 3 : ℝ)) * Real.logb 2 n ^ c)) ≤
          |stat P (window (List.ofFn x) i) (shift S ℓ) - stat P (window (List.ofFn y) i) (shift S ℓ)| := by sorry

end QuasiPolyTrace
